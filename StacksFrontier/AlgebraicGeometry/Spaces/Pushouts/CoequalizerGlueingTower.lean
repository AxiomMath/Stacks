module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraOverHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent

/-!
# The tower of glueing coequalizers along the infinitesimal neighbourhoods of `Z`

In the proper-modification situation of Stacks 0AGH -- a locally Noetherian algebraic space `X`
over `S`, a closed immersion `i : Z ⟶ X` with complementary open `U`, and a proper `f : X' ⟶ X`
which is an isomorphism over `U` -- let `𝓘 ⊆ 𝒪_X` be the quasi-coherent ideal of `Z` and let
`Z_n ⊆ X` be the closed subspace cut out by `𝓘ⁿ`, the `n`th order infinitesimal neighbourhood
of `Z` in `X`. Stacks 0AGJ considers the coequalizers `X_n` of the kernel pairs of
`Y_n = X' ⨿ Z_n ⟶ X` and the tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X` they form, and Stacks 0AGK shows
that for `n` large enough some `X_n ⟶ X_{n+m}` factors through a closed immersion
`X ⟶ X_{n+m}`.

This file builds the tower of Stacks 0AGJ from the infinitesimal neighbourhoods, and proves the
geometric half of Stacks 0AGK: the reduction of the factorization to a statement about the
direct-image algebras `𝒜_n = (X_n ⟶ X)_* 𝒪`.

## Main definitions

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.closedIdeal`: the ideal `𝓘` of `Z`.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.neighbourhood`: the closed subspace
  `Z_{n+1}` cut out by `𝓘ⁿ⁺¹` (the source indexes from `1`, the tower here from `0`).
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.neighbourhoodSystem`: the system
  `Z_1 ⊆ Z_2 ⊆ …` as an `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem`.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.neighbourhoodCoequalizer`: a coequalizer
  `X_n` of the kernel pair of `Y_n ⟶ X`, from the conclusion of Stacks 0AGG.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem.towerTransition`: the
  composite `X_n ⟶ X_{n+m}` of the tower of Stacks 0AGJ.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem.FactorsThroughSection`:
  the conclusion of Stacks 0AGK for one pair `(n, n + m)`.

## Main results

* `AlgebraicGeometry.Space.isProper_coprodDesc`: a morphism out of a binary coproduct of
  algebraic spaces whose two restrictions are proper is proper; in particular each
  `Y_n ⟶ X` is proper (`isProper_glueMapAt`), so Stacks 0AGG applies to it.
* `AlgebraicGeometry.Space.exists_section_of_range_le`: for algebraic spaces `P` finite and `Q`
  affine over `X` and a morphism `t : Q ⟶ P` over `X`, if `𝒪_X ⟶ Q_* 𝒪` is injective and the image
  of `t♯ : P_* 𝒪 ⟶ Q_* 𝒪` lies in the image of `𝒪_X`, then `t` factors as `Q ⟶ X ⟶ P` through a
  section `X ⟶ P` of `P ⟶ X`, which is a closed immersion.
* `CoequalizerGlueSituation.ClosedSubspaceSystem.factorsThroughSection_of_range_le`: the same
  for the tower: Stacks 0AGK for the pair `(n, n + m)` follows from the two algebraic properties
  of `𝒜_{n+m} ⟶ 𝒜_n ⟵ 𝒪_X`.

## Implementation notes

Stacks 0AGG is the hypothesis `hAGG : ProperKernelPairCoequalizers` of the construction of the
coequalizers, as in Stacks 0AGI.

## References

* [Stacks Project, Tag 0AGJ](https://stacks.math.columbia.edu/tag/0AGJ)
* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Properness of a morphism out of a binary coproduct -/

section Coproduct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The two summands of a binary coproduct, as a family indexed by `ULift Bool`. -/
def binarySummand (A C : AlgebraicSpaces B S hS) : ULift.{u} Bool → AlgebraicSpaces B S hS
  | ⟨false⟩ => A
  | ⟨true⟩ => C

/-- The two coproduct inclusions into `A ⨿ C`, as a cofan of
`AlgebraicGeometry.Space.binarySummand`. -/
def binarySummandIncl (A C : AlgebraicSpaces B S hS) : ∀ b, binarySummand A C b ⟶ A ⨿ C
  | ⟨false⟩ => coprod.inl
  | ⟨true⟩ => coprod.inr

/-- `A ⨿ C` is the colimit of the two-member cofan of its coproduct inclusions. -/
def isColimitBinarySummandCofan (A C : AlgebraicSpaces B S hS) :
    IsColimit (Cofan.mk (A ⨿ C) (binarySummandIncl A C)) := by
  refine Cofan.IsColimit.mk _ (fun s => coprod.desc (s.inj ⟨false⟩) (s.inj ⟨true⟩)) ?_
    fun s m hm => coprod.hom_ext ((hm ⟨false⟩).trans (coprod.inl_desc _ _).symm)
      ((hm ⟨true⟩).trans (coprod.inr_desc _ _).symm)
  rintro s ⟨_ | _⟩
  · exact coprod.inl_desc _ _
  · exact coprod.inr_desc _ _

/-- **A morphism out of a binary coproduct of algebraic spaces is proper when its two
restrictions are.** The inclusion of the algebraic spaces into the fppf sheaves creates
countable coproducts, so the coproduct is one of sheaves and
`AlgebraicGeometry.Space.isProper_of_isColimit_cofan` applies. -/
theorem isProper_coprodDesc {A C X : AlgebraicSpaces B S hS} (a : A ⟶ X) (c : C ⟶ X)
    (ha : IsProper B S hS a.hom) (hc : IsProper B S hS c.hom) :
    IsProper B S hS (coprod.desc a c).hom := by
  let F := algebraicSpacesToSheaf B S hS
  have hP : IsColimit (Cofan.mk (F.obj (A ⨿ C)) fun b => F.map (binarySummandIncl A C b)) :=
    isColimitCofanMkObjOfIsColimit F (binarySummand A C) (binarySummandIncl A C)
      (isColimitBinarySummandCofan A C)
  refine isProper_of_isColimit_cofan B S hS (fun b => F.map (binarySummandIncl A C b)) hP
    (fun b => (binarySummand A C b).property) (A ⨿ C).property X.property _ ?_
  rintro ⟨_ | _⟩
  · change IsProper B S hS ((coprod.inl ≫ coprod.desc a c : A ⟶ X).hom)
    rwa [coprod.inl_desc]
  · change IsProper B S hS ((coprod.inr ≫ coprod.desc a c : C ⟶ X).hom)
    rwa [coprod.inr_desc]

end Coproduct

/-! ### Factoring through a section, from the direct-image algebras -/

section Section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an algebraic space over `X`, as a morphism over `X` to `X` itself. -/
abbrev toIdOver {X : AlgebraicSpaces B S hS} (Q : Over X) : Q ⟶ Over.mk (𝟙 X) :=
  Over.homMk Q.hom

variable {B S hS} {X : AlgebraicSpaces B S hS} {P Q : Over X} (t : Q ⟶ P)

/-- The image of `t♯ : P_* 𝒪 ⟶ Q_* 𝒪` lies in the image of the structure map `𝒪_X ⟶ Q_* 𝒪`
over an étale chart `V`. -/
def RangeLeStructure (V : SmallEtale B S hS X.1) : Prop :=
  ∀ b : (pushforwardAlgebra B S hS P).right.obj.obj (op V),
    ∃ r : (pushforwardAlgebra B S hS (Over.mk (𝟙 X))).right.obj.obj (op V),
      (pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op V) r =
        (pushforwardRingMap B S hS t).hom.app (op V) b

variable (hinj : ∀ V : SmallEtale B S hS X.1,
    Function.Injective ((pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op V)))
  (hrange : ∀ V : SmallEtale B S hS X.1, RangeLeStructure t V)

/-- The chart value of the morphism `P_* 𝒪 ⟶ 𝒪_X` through which `t♯` factors, when the structure
map `𝒪_X ⟶ Q_* 𝒪` is injective and contains the image of `t♯`. -/
def sectionRingHom (V : SmallEtale B S hS X.1) :
    (pushforwardAlgebra B S hS P).right.obj.obj (op V) →+*
      (pushforwardAlgebra B S hS (Over.mk (𝟙 X))).right.obj.obj (op V) :=
  let e := ((pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op V)).hom
  (RingEquiv.ofBijective e.rangeRestrict
      ⟨fun _ _ h => hinj V (congrArg Subtype.val h),
        e.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (((pushforwardRingMap B S hS t).hom.app (op V)).hom.codRestrict e.range
      fun b => (hrange V b).imp fun _ h => h)

/-- `AlgebraicGeometry.Space.sectionRingHom` followed by the structure map `𝒪_X ⟶ Q_* 𝒪` is
`t♯`. -/
theorem pushforwardRingMap_sectionRingHom (V : SmallEtale B S hS X.1)
    (b : (pushforwardAlgebra B S hS P).right.obj.obj (op V)) :
    (pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op V)
        (sectionRingHom t hinj hrange V b) =
      (pushforwardRingMap B S hS t).hom.app (op V) b := by
  exact congrArg Subtype.val <| RingEquiv.apply_symm_apply
    (RingEquiv.ofBijective _ ⟨fun _ _ h => hinj V (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩) _

/-- The chart values of `AlgebraicGeometry.Space.sectionRingHom` commute with restriction. -/
theorem sectionRingHom_naturality {V W : SmallEtale B S hS X.1} (g : op V ⟶ op W)
    (b : (pushforwardAlgebra B S hS P).right.obj.obj (op V)) :
    sectionRingHom t hinj hrange W ((pushforwardAlgebra B S hS P).right.obj.map g b) =
      (pushforwardAlgebra B S hS (Over.mk (𝟙 X))).right.obj.map g
        (sectionRingHom t hinj hrange V b) := by
  apply hinj W
  rw [pushforwardRingMap_sectionRingHom]
  have h1 := ConcreteCategory.congr_hom
    ((pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.naturality g)
    (sectionRingHom t hinj hrange V b)
  have h2 := ConcreteCategory.congr_hom ((pushforwardRingMap B S hS t).hom.naturality g) b
  simp only [CommRingCat.comp_apply] at h1 h2
  rw [h2, h1, pushforwardRingMap_sectionRingHom]

/-- The morphism of sheaves of rings `P_* 𝒪 ⟶ 𝒪_X` through which `t♯` factors. -/
def sectionRingSheafHom :
    (pushforwardAlgebra B S hS P).right ⟶ (pushforwardAlgebra B S hS (Over.mk (𝟙 X))).right where
  hom :=
    { app := fun V => CommRingCat.ofHom (R := (pushforwardAlgebra B S hS P).right.obj.obj V)
        (S := (pushforwardAlgebra B S hS (Over.mk (𝟙 X))).right.obj.obj V)
        (sectionRingHom t hinj hrange V.unop)
      naturality := fun V W g => CommRingCat.hom_ext <| RingHom.ext fun b =>
        sectionRingHom_naturality t hinj hrange (V := V.unop) (W := W.unop) g b }

/-- The morphism of `𝒪_X`-algebras `P_* 𝒪 ⟶ 𝒪_X` through which `t♯` factors. -/
def sectionAlgebraHom :
    pushforwardAlgebra B S hS P ⟶ pushforwardAlgebra B S hS (Over.mk (𝟙 X)) where
  right := sectionRingSheafHom t hinj hrange
  comm U r := by
    apply hinj U.unop
    change (pushforwardRingMap B S hS (toIdOver B S hS Q)).hom.app (op U.unop)
        (sectionRingHom t hinj hrange U.unop _) = _
    rw [pushforwardRingMap_sectionRingHom]
    exact ((pushforwardAlgebraMap B S hS t).comm U r).trans
      ((pushforwardAlgebraMap B S hS (toIdOver B S hS Q)).comm U r).symm

/-- `AlgebraicGeometry.Space.sectionAlgebraHom` followed by `𝒪_X ⟶ Q_* 𝒪` is `t♯`. -/
theorem sectionAlgebraHom_comp :
    sectionAlgebraHom t hinj hrange ≫ pushforwardAlgebraMap B S hS (toIdOver B S hS Q) =
      pushforwardAlgebraMap B S hS t := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun V => CommRingCat.hom_ext <|
    RingHom.ext fun b => ?_)))
  exact pushforwardRingMap_sectionRingHom t hinj hrange V.unop b

variable (hP : IsFinite B S hS P.hom.hom)

/-- `P` as an algebraic space affine over `X`. -/
abbrev finiteAffineOver : AffineOver B S hS X := ⟨P, IsFinite.isAffineHom hP⟩

/-- The section `X ⟶ P` over `X` corresponding to the factorization `P_* 𝒪 ⟶ 𝒪_X` of `t♯`
(Stacks 081V). -/
def sectionOver : Over.mk (𝟙 X) ⟶ P :=
  (overHomEquivPushforwardAlgebraHom B S hS (Over.mk (𝟙 X)) (finiteAffineOver hP)).symm
    (sectionAlgebraHom t hinj hrange)

/-- The morphism of direct-image algebras of `AlgebraicGeometry.Space.sectionOver` is
`AlgebraicGeometry.Space.sectionAlgebraHom`. -/
theorem pushforwardAlgebraMap_sectionOver :
    pushforwardAlgebraMap B S hS (sectionOver t hinj hrange hP) = sectionAlgebraHom t hinj hrange :=
  (overHomEquivPushforwardAlgebraHom B S hS (Over.mk (𝟙 X))
    (finiteAffineOver hP)).apply_symm_apply _

/-- The morphism of direct-image algebras of `Q ⟶ X ⟶ P` is `t♯`. -/
theorem pushforwardAlgebraMap_toIdOver_comp_sectionOver :
    pushforwardAlgebraMap B S hS (toIdOver B S hS Q ≫ sectionOver t hinj hrange hP) =
      pushforwardAlgebraMap B S hS t := by
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_sectionOver, sectionAlgebraHom_comp]

/-- `t` factors as `Q ⟶ X ⟶ P` through the section `AlgebraicGeometry.Space.sectionOver`. -/
theorem toIdOver_comp_sectionOver : toIdOver B S hS Q ≫ sectionOver t hinj hrange hP = t :=
  eq_of_pushforwardAlgebraMap_eq B S hS (finiteAffineOver hP)
    (pushforwardAlgebraMap_toIdOver_comp_sectionOver t hinj hrange hP)

/-- `AlgebraicGeometry.Space.sectionOver` is a section of `P ⟶ X`. -/
theorem sectionOver_left_comp : (sectionOver t hinj hrange hP).left ≫ P.hom = 𝟙 X :=
  Over.w (sectionOver t hinj hrange hP)

/-- The section `AlgebraicGeometry.Space.sectionOver` of the separated `P ⟶ X` is a closed
immersion. -/
theorem isClosedImmersion_sectionOver_left :
    IsClosedImmersion B S hS (sectionOver t hinj hrange hP).left.hom :=
  isClosedImmersion_of_isSeparated_of_section B S hS P.hom.hom
    (isSeparated_of_isFinite B S hS P.hom.hom P.left.property X.property hP) _
    (congrArg (fun k : X ⟶ X => k.hom) (sectionOver_left_comp t hinj hrange hP))

include hinj hrange hP in
/-- **A morphism `t : Q ⟶ P` over `X`, with `P` finite and `Q` affine over `X`, factors through a
closed-immersion section of `P ⟶ X`** as soon as the structure map `𝒪_X ⟶ Q_* 𝒪` is injective and
its image contains that of `t♯ : P_* 𝒪 ⟶ Q_* 𝒪`. The section is the morphism over `X`
corresponding to the factorization `P_* 𝒪 ⟶ 𝒪_X` of `t♯` (Stacks 081V), and a section of the
separated morphism `P ⟶ X` is a closed immersion. -/
theorem exists_section_of_range_le :
    ∃ c : X ⟶ P.left, IsClosedImmersion B S hS c.hom ∧ c ≫ P.hom = 𝟙 X ∧
      Q.hom ≫ c = t.left :=
  ⟨(sectionOver t hinj hrange hP).left, isClosedImmersion_sectionOver_left t hinj hrange hP,
    sectionOver_left_comp t hinj hrange hP,
    congrArg (fun k : Q ⟶ P => k.left) (toIdOver_comp_sectionOver t hinj hrange hP)⟩

end Section

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### The infinitesimal neighbourhoods of `Z` -/

/-- The quasi-coherent ideal `𝓘 = Ker(𝒪_X ⟶ i_* 𝒪_Z)` of the closed subspace `Z` (Stacks 03MB). -/
def closedIdeal : IdealSheaves T.B T.S T.hS T.X T.hX :=
  kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk T.i : T.closedSpace ⟶ T.targetSpace)

/-- The ideal `𝓘` of `Z` is quasi-coherent. -/
theorem isQuasicoherentOnSite_closedIdeal :
    T.closedIdeal.toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernelIdealSheaf T.B T.S T.hS _
    (isQuasiCompact_of_isClosedImmersion' T.B T.S T.hS T.hi)

/-- The ideal `𝓘ⁿ⁺¹` cutting out the infinitesimal neighbourhood `Z_{n+1}` of `Z` in `X`. -/
def neighbourhoodIdeal (n : ℕ) : IdealSheaves T.B T.S T.hS T.X T.hX :=
  Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O) T.closedIdeal (n + 1)

/-- The powers of the ideal of `Z` are quasi-coherent, because `X` is locally Noetherian. -/
theorem isQuasicoherentOnSite_neighbourhoodIdeal (n : ℕ) :
    (T.neighbourhoodIdeal n).toSheafOfModules.IsQuasicoherentOnSite := by
  have : Fact (HasEtaleLocalProperty T.B T.S T.hS T.X
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨T.locallyNoetherian⟩
  have h := (isCoherent_idealPowModule_of_isQuasicoherentOnSite T.B T.S T.hS T.X T.hX
    T.closedIdeal (n + 1)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O))
    (isCoherent_structureSheaf T.B T.S T.hS T.X T.hX)
    T.isQuasicoherentOnSite_closedIdeal).toIsQuasicoherentOnSite
  have e : idealPowSubmodule T.closedIdeal (n + 1)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)) =
        T.neighbourhoodIdeal n := by
    rw [idealPowSubmodule_eq_idealPowSmul]
    exact Stacks.Sites.idealSmul_top_eq (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
      (T.neighbourhoodIdeal n)
  rwa [← e]

/-- **The infinitesimal neighbourhood `Z_{n+1}` of `Z` in `X`**: the closed subspace cut out by
`𝓘ⁿ⁺¹` (Stacks 03MB, surjectivity of the correspondence). -/
def neighbourhood (n : ℕ) : ClosedSubspaces T.B T.S T.hS T.X :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite T.B T.S T.hS T.targetSpace
    (T.neighbourhoodIdeal n) (T.isQuasicoherentOnSite_neighbourhoodIdeal n)).choose

/-- The ideal of `Z_{n+1}` is `𝓘ⁿ⁺¹`. -/
theorem definingIdealSheaf_neighbourhood (n : ℕ) :
    definingIdealSheaf T.B T.S T.hS T.targetSpace (T.neighbourhood n) = T.neighbourhoodIdeal n :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite T.B T.S T.hS T.targetSpace
    (T.neighbourhoodIdeal n) (T.isQuasicoherentOnSite_neighbourhoodIdeal n)).choose_spec

/-- `Z_{n+1} ⊆ Z_{n+2}`. -/
theorem neighbourhood_le_succ (n : ℕ) : (T.neighbourhood n).1 ≤ (T.neighbourhood (n + 1)).1 :=
  le_of_definingIdealSheaf_le T.B T.S T.hS T.targetSpace _ _ (by
    rw [definingIdealSheaf_neighbourhood, definingIdealSheaf_neighbourhood]
    exact Stacks.Sites.idealPow_antitone T.closedIdeal (by omega : n + 1 ≤ n + 1 + 1))

/-- **The system `Z_1 ⊆ Z_2 ⊆ Z_3 ⊆ …` of infinitesimal neighbourhoods of `Z` in `X`**, over which
the glueing construction is repeated in Stacks 0AGJ. Its `n`th member is `Z_{n+1}`. -/
def neighbourhoodSystem : T.ClosedSubspaceSystem where
  space n := ⟨(T.neighbourhood n).1.toFunctor, (T.neighbourhood n).2.1⟩
  toTarget n := ObjectProperty.homMk (T.neighbourhood n).1.ι
  isClosedImmersion_toTarget n := (T.neighbourhood n).2.2
  step n := ObjectProperty.homMk (Subfunctor.homOfLe (T.neighbourhood_le_succ n))
  step_comp_toTarget n :=
    ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι (T.neighbourhood_le_succ n))

/-- The kernel of `𝒪_X ⟶ (Z_{n+1} ⟶ X)_* 𝒪` is `𝓘ⁿ⁺¹`. -/
theorem kernelIdealSheaf_neighbourhoodSystem_toTarget (n : ℕ) :
    kernelIdealSheaf T.B T.S T.hS (T.neighbourhoodSystem.toTarget n) = T.neighbourhoodIdeal n :=
  show kernelIdealSheaf T.B T.S T.hS (ObjectProperty.homMk (T.neighbourhood n).1.ι :
      (⟨(T.neighbourhood n).1.toFunctor, (T.neighbourhood n).2.1⟩ : AlgebraicSpaces T.B T.S T.hS) ⟶
        T.targetSpace) = _ from
  (kernelIdealSheaf_eq_definingIdealSheaf T.B T.S T.hS T.targetSpace (T.neighbourhood n)).trans
    (T.definingIdealSheaf_neighbourhood n)

/-- The closed immersion `Z ⟶ X` factors through each infinitesimal neighbourhood `Z_{n+1}`:
the ideal `𝓘ⁿ⁺¹` of `Z_{n+1}` lies in the ideal `𝓘` of `Z`. -/
theorem exists_lift_neighbourhoodSystem (n : ℕ) :
    ∃ l : T.closedSpace ⟶ T.neighbourhoodSystem.space n,
      l ≫ T.neighbourhoodSystem.toTarget n = ObjectProperty.homMk T.i := by
  refine (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf T.B T.S T.hS
    (X := T.targetSpace) (T.neighbourhood n)
    (ObjectProperty.homMk T.i : T.closedSpace ⟶ T.targetSpace)).2 ?_
  rw [definingIdealSheaf_neighbourhood, neighbourhoodIdeal]
  exact (Stacks.Sites.idealPow_antitone T.closedIdeal (by omega : 1 ≤ n + 1)).trans
    (Stacks.Sites.idealPow_one T.closedIdeal).le

/-- Each `g_{n+1} : Y_{n+1} = X' ⨿ Z_{n+1} ⟶ X` is surjective: `g : X' ⨿ Z ⟶ X` is
(`AlgebraicGeometry.Space.CoequalizerGlueSituation.isSurjective_glueMap`), and it factors through
`g_{n+1}` by the lift of `Z ⟶ X` to `Z_{n+1}`. -/
theorem isSurjective_neighbourhoodSystem_glueMapAt (n : ℕ) :
    IsSurjective T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n).hom := by
  obtain ⟨l, hl⟩ := T.exists_lift_neighbourhoodSystem n
  have hfac : coprod.map (𝟙 T.modificationSpace) l ≫ T.neighbourhoodSystem.glueMapAt n =
      T.glueMap := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_map_assoc, Category.id_comp, ClosedSubspaceSystem.glueMapAt,
        coprod.inl_desc, inl_glueMap]
    · rw [coprod.inr_map_assoc, ClosedSubspaceSystem.glueMapAt, coprod.inr_desc, hl,
        inr_glueMap]
  intro x
  obtain ⟨y, hy⟩ := T.isSurjective_glueMap x
  rw [← hfac] at hy
  change pointsMap T.B T.S T.hS _ ((coprod.map (𝟙 T.modificationSpace) l).hom ≫
    (T.neighbourhoodSystem.glueMapAt n).hom) y = x at hy
  rw [pointsMap_comp] at hy
  exact ⟨_, hy⟩

namespace ClosedSubspaceSystem

variable {T} (N : T.ClosedSubspaceSystem)

/-! ### The tower of coequalizers -/

/-- Each `g_n : Y_n = X' ⨿ Z_n ⟶ X` is proper: it is the proper `f` on `X'` and a closed
immersion on `Z_n`. -/
theorem isProper_glueMapAt (n : ℕ) : IsProper T.B T.S T.hS (N.glueMapAt n).hom :=
  isProper_coprodDesc _ _ T.hf
    (isProper_of_isClosedImmersion T.B T.S T.hS (N.space n).property T.hX _
      (N.isClosedImmersion_toTarget n))

variable (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (N.glueMapAt n))

/-- **The composite `X_n ⟶ X_{n+m}` of the tower of Stacks 0AGJ.** -/
def towerTransition (n : ℕ) : ∀ m : ℕ, (D n).space ⟶ (D (n + m)).space
  | 0 => 𝟙 _
  | m + 1 => towerTransition n m ≫ N.towerMap D (n + m)

/-- The transitions `X_n ⟶ X_{n+m}` of the tower are morphisms over `X`. -/
theorem towerTransition_comp_toTarget (n : ℕ) :
    ∀ m : ℕ, N.towerTransition D n m ≫ (D (n + m)).toTarget = (D n).toTarget
  | 0 => Category.id_comp _
  | m + 1 => by
    rw [towerTransition, Category.assoc]
    change N.towerTransition D n m ≫ N.towerMap D (n + m) ≫ (D (n + m + 1)).toTarget = _
    rw [N.towerMap_comp_toTarget D (n + m), towerTransition_comp_toTarget n m]

/-- **The conclusion of Stacks 0AGK for the pair `(n, n + m)`**: `X_n ⟶ X_{n+m}` factors through
a closed immersion `X ⟶ X_{n+m}`. The closed immersion is moreover a section of
`X_{n+m} ⟶ X`, and the first factor is the morphism `X_n ⟶ X`. -/
def FactorsThroughSection (n m : ℕ) : Prop :=
  ∃ c : T.targetSpace ⟶ (D (n + m)).space, IsClosedImmersion T.B T.S T.hS c.hom ∧
    c ≫ (D (n + m)).toTarget = 𝟙 _ ∧ (D n).toTarget ≫ c = N.towerTransition D n m

/-- `X_n` as an algebraic space over `X`. -/
abbrev stageOver (n : ℕ) : Over T.targetSpace := Over.mk (D n).toTarget

/-- The transition `X_n ⟶ X_{n+m}`, as a morphism over `X`. -/
abbrev towerTransitionOver (n m : ℕ) : N.stageOver D n ⟶ N.stageOver D (n + m) :=
  Over.homMk (N.towerTransition D n m) (N.towerTransition_comp_toTarget D n m)

/-- **Stacks 0AGK for one pair, from the direct-image algebras.** Write `𝒜_k = (X_k ⟶ X)_* 𝒪`. If
`X_{n+m} ⟶ X` is finite, `X_n ⟶ X` is affine, `𝒪_X ⟶ 𝒜_n` is injective and the image of
`𝒜_{n+m} ⟶ 𝒜_n` lies in that of `𝒪_X`, then `X_n ⟶ X_{n+m}` factors through a closed immersion
`X ⟶ X_{n+m}` which is a section of `X_{n+m} ⟶ X`. -/
theorem factorsThroughSection_of_range_le (n m : ℕ)
    (hfin : IsFinite T.B T.S T.hS (D (n + m)).toTarget.hom)
    (hinj : ∀ V : SmallEtale T.B T.S T.hS T.X, Function.Injective
      ((pushforwardRingMap T.B T.S T.hS (toIdOver T.B T.S T.hS (N.stageOver D n))).hom.app (op V)))
    (hrange : ∀ V : SmallEtale T.B T.S T.hS T.X,
      RangeLeStructure (N.towerTransitionOver D n m) V) :
    N.FactorsThroughSection D n m :=
  exists_section_of_range_le (N.towerTransitionOver D n m) hinj hrange hfin

end ClosedSubspaceSystem

/-! ### The coequalizers of the infinitesimal neighbourhoods -/

variable (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)

/-- **A coequalizer `X_{n+1}` of the kernel pair of `Y_{n+1} = X' ⨿ Z_{n+1} ⟶ X`**, chosen from
the conclusion of Stacks 0AGG, carried as the hypothesis `hAGG`. -/
def neighbourhoodCoequalizer (n : ℕ) :
    KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n) :=
  (hAGG.nonempty_coequalizer _ T.locallyNoetherian
    (T.neighbourhoodSystem.isProper_glueMapAt n)).some

/-- **The tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X` of Stacks 0AGJ**, from the conclusion of Stacks 0AGG:
each `X_{n+1} ⟶ X_{n+2}` is a morphism over `X` (`towerMap_comp_toTarget`), and each `X_{n+1} ⟶ X`
is a finite universal homeomorphism. -/
theorem neighbourhoodTower_spec (n : ℕ) :
    T.neighbourhoodSystem.towerMap (T.neighbourhoodCoequalizer hAGG) n ≫
        (T.neighbourhoodCoequalizer hAGG (n + 1)).toTarget =
      (T.neighbourhoodCoequalizer hAGG n).toTarget ∧
    IsFinite T.B T.S T.hS (T.neighbourhoodCoequalizer hAGG n).toTarget.hom ∧
    UniversalHomeomorphism T.B T.S T.hS (T.neighbourhoodCoequalizer hAGG n).toTarget.hom :=
  ⟨T.neighbourhoodSystem.towerMap_comp_toTarget _ n,
    hAGG.isFinite_toTarget _ T.locallyNoetherian (T.neighbourhoodSystem.isProper_glueMapAt n) _,
    hAGG.universalHomeomorphism_toTarget _ T.locallyNoetherian
      (T.neighbourhoodSystem.isProper_glueMapAt n) (T.isSurjective_neighbourhoodSystem_glueMapAt n)
      _⟩

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
