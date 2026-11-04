module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.ChartPrecomp
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.AdjointEpi
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.DirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Relative very ampleness through the morphism `r_{L, ψ}` into a relative `Proj`

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module. This file states and
compares two conditions of [Stacks, Tag 01VR] that are phrased through the morphism
`r_{L, ψ} : X ⟶ Proj_S(A)` of [Stacks, Tag 01O9].

* Clause (3): there are a quasi-coherent graded `𝒪_S`-algebra `A` generated in degree one and a
  map of graded `𝒪_X`-algebras `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}` such that `f^* A_1 ⟶ L` is
  surjective and `r_{L, ψ} : X ⟶ Proj_S(A)` is an immersion.
* Clause (4): `f` is quasi-separated, the canonical map `f^* f_* L ⟶ L` is surjective and the
  associated morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` is an immersion.

Surjectivity of `f^* A_1 ⟶ L` makes `U(ψ) = X`, so that `r_{L, ψ}` is a morphism out of `X`.

The implications proved here are (3) ⟹ (1), (4) ⟹ (1) and (4) ⟹ (3), (1) being relative very
ampleness in the sense of [Stacks, Tag 01VM]. For (4) ⟹ (1) the immersion is `r_{L, ψ}` itself,
and the pullback of `𝒪_{𝐏(f_* L)}(1)` along it is `L`
(`Stacks.VeryAmpleGlue.pullbackTwistOneIso`). For (3) ⟹ (1) the source composes `r_{L, ψ}` with the
closed immersion `Proj_S(A) ⟶ 𝐏(A_1)` of [Stacks, Tag 07ZK]. Here the morphism
`X ⟶ 𝐏(A_1)` is taken to be `r_{L, ψ ∘ c}` for the canonical map `c : Sym(A_1) ⟶ A`: its charts
are those of `r_{L, ψ}` followed by `Spec` of surjections of rings
(`Stacks.Tag01VMVeryAmple.chartsAreImmersions_precomp`), so it is an immersion, and the pullback
of `𝒪_{𝐏(A_1)}(1)` along it is `L` by the same `Stacks.VeryAmpleGlue.pullbackTwistOneIso`.

## Main definitions

* `Stacks.Tag01VMVeryAmple.degreeOneMap`: the degree-one component `f^* A_1 ⟶ L` of a graded map
  `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}`.
* `Stacks.Tag01VMVeryAmple.toRelativeProj`: the morphism `r_{L, ψ} : X ⟶ Proj_S(A)` when
  `U(ψ) = X`.
* `Stacks.Tag01VMVeryAmple.HasImmersionToRelativeProj`: **clause (3) of Tag 01VR.**
* `Stacks.Tag01VMVeryAmple.directImageSymPowerMap`: the graded map
  `f^* Sym(f_* L) ⟶ ⨁_{n ≥ 0} L^{⊗ n}` extending the canonical map `f^* f_* L ⟶ L`.
* `Stacks.Tag01VMVeryAmple.IsImmersionDirectImageBundle`: **clause (4) of Tag 01VR.**

## Main results

* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_hasImmersionToRelativeProj`: (3) ⟹ (1).
* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_isImmersionDirectImageBundle`: (4) ⟹ (1).
* `Stacks.Tag01VMVeryAmple.hasImmersionToRelativeProj_of_isImmersionDirectImageBundle`:
  (4) ⟹ (3).

## Implementation notes

**The graded map `ψ` is recorded in adjoint form**, as a
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`: its components are maps
`A_n ⟶ f_* L^{⊗ n}`, multiplicative across degrees. This is the datum of [Stacks, Tag 01O8] the
construction of `r_{L, ψ}` consumes, and it carries the same information as a map of graded
`𝒪_X`-algebras out of `f^* A` by the adjunction `f^* ⊣ f_*`; the surjectivity condition is stated
on the adjoint `f^* A_1 ⟶ L` of the degree-one component, `degreeOneMap`. The unit axiom
`ψ(1) = 1` is not imposed, as in [Stacks, Tag 01O8]'s datum; this only enlarges clause (3).

**Generation in degree one is over `A_0`**,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne`, which is weaker than
generation over `𝒪_S`; clause (3) is accordingly at least as general as the source's.

## References

* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.QuasiProjectiveCompactification
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe u

namespace Stacks.Tag01VMVeryAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-! ### The degree-one component and `U(ψ) = X` -/

section Generic

variable {A : SheafGradedAlgebra.{u} S} (P : GradedPowerMap A f)

/-- The degree-one component of a graded map `ψ` in adjoint form, read into `f_* L` through
`L^{⊗ 1} ≅ L`. -/
abbrev degreeOneAdjoint : A.piece ((1 : ℕ) : ℤ) ⟶ (Scheme.Modules.pushforward f).obj P.L :=
  P.ψ 1 ≫ (Scheme.Modules.pushforward f).map
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow P.L).hom

/-- **The degree-one component `f^* A_1 ⟶ L` of a graded map `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}`**,
the adjoint of `A_1 ⟶ f_* L`. -/
def degreeOneMap : (Scheme.Modules.pullback f).obj (A.piece ((1 : ℕ) : ℤ)) ⟶ P.L :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (degreeOneAdjoint P)

/-- The degree-one value of `ψ`, read in `L`, does not vanish exactly where its value in
`L^{⊗ 1}` does not. -/
theorem mem_nonvanishingLocusOn_degreeOneAdjoint_iff (V : S.Opens)
    (a : Γ(A.piece ((1 : ℕ) : ℤ), V)) (x : X) :
    x ∈ nonvanishingLocusOn P.L (f ⁻¹ᵁ V) ((degreeOneAdjoint P).app V a) ↔
      x ∈ P.nonvanishingOpenAt 1 V a :=
  Set.ext_iff.mp (Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow P.L) (f ⁻¹ᵁ V) (P.value 1 V a)) x

/-- **The degree-one values of `ψ` cover `X` as soon as `f^* A_1 ⟶ L` is surjective**, by sections
over affine opens of the base. -/
theorem exists_mem_nonvanishingOpenAt_of_epi [Epi (degreeOneMap P)] (x : X) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (a : Γ(A.piece ((1 : ℕ) : ℤ), V)),
      x ∈ P.nonvanishingOpenAt 1 V a := by
  have : Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (degreeOneAdjoint P)) := ‹Epi (degreeOneMap P)›
  obtain ⟨V, hV, a, hx⟩ := exists_mem_nonvanishingLocusOn_of_epi_adjoint f
    (degreeOneAdjoint P) x
  exact ⟨V, hV, a, (mem_nonvanishingLocusOn_degreeOneAdjoint_iff P V a x).mp hx⟩

/-- **`f^* A_1 ⟶ L` is surjective as soon as the degree-one values of `ψ` cover `X`.** -/
theorem epi_degreeOneMap_of_forall
    (h : ∀ x : X, ∃ (V : S.Opens) (a : Γ(A.piece ((1 : ℕ) : ℤ), V)),
      x ∈ P.nonvanishingOpenAt 1 V a) :
    Epi (degreeOneMap P) :=
  epi_adjoint_of_forall_mem_nonvanishingLocusOn f (degreeOneAdjoint P) fun x => by
    obtain ⟨V, a, hx⟩ := h x
    exact ⟨V, a, (mem_nonvanishingLocusOn_degreeOneAdjoint_iff P V a x).mpr hx⟩

/-- **`U(ψ) = X`** when the degree-one values of `ψ` over affine opens of the base cover `X`. -/
theorem coveringOpen_eq_top_of_forall
    (h : ∀ x : X, ∃ (V : S.Opens) (_ : IsAffineOpen V) (a : Γ(A.piece ((1 : ℕ) : ℤ), V)),
      x ∈ P.nonvanishingOpenAt 1 V a) :
    P.coveringOpen = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨V, hV, a, hx⟩ := h x
  exact P.nonvanishingOpenAt_le_coveringOpen 0 V hV a hx

/-- **`U(ψ) = X` when `f^* A_1 ⟶ L` is surjective.** -/
theorem coveringOpen_eq_top_of_epi (h : Epi (degreeOneMap P)) : P.coveringOpen = ⊤ :=
  coveringOpen_eq_top_of_forall P (exists_mem_nonvanishingOpenAt_of_epi P)

/-- **The morphism `r_{L, ψ} : X ⟶ Proj_S(A)` of [Stacks, Tag 01O9]** when its domain of
definition `U(ψ)` is all of `X`. -/
def toRelativeProj (hP : P.coveringOpen = ⊤) : X ⟶ (relativeProj A).scheme :=
  X.topIso.inv ≫ (X.isoOfEq hP).inv ≫ P.globalMorphism (relativeProj A)

/-- `r_{L, ψ}` is a morphism over the base. -/
theorem toRelativeProj_comp_toBase (hP : P.coveringOpen = ⊤) :
    toRelativeProj P hP ≫ (relativeProj A).toBase = f := by
  rw [toRelativeProj, Category.assoc, Category.assoc, P.globalMorphism_comp_toBase (relativeProj A),
    GradedPowerMap.toBase, ← Category.assoc (X.isoOfEq hP).inv, Scheme.isoOfEq_inv_ι,
    ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

/-- `r_{L, ψ}` is an immersion exactly when the morphism out of `U(ψ)` is. -/
theorem isImmersion_toRelativeProj_iff (hP : P.coveringOpen = ⊤) :
    IsImmersion (toRelativeProj P hP) ↔ IsImmersion (P.globalMorphism (relativeProj A)) := by
  let e : X ≅ P.coveringOpen.toScheme := X.topIso.symm ≪≫ (X.isoOfEq hP).symm
  have he : toRelativeProj P hP = e.hom ≫ P.globalMorphism (relativeProj A) := by
    simp only [toRelativeProj, e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : P.globalMorphism (relativeProj A) = e.inv ≫ toRelativeProj P hP := by
      rw [he, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  · rw [he]
    infer_instance

end Generic

/-! ### Stacks Tag 01VR, clause (3) -/

/-- **Clause (3) of Stacks Tag 01VR.** There are a quasi-coherent graded `𝒪_S`-algebra `A`
generated in degree one and a map of graded algebras `ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}`, recorded in
adjoint form as a `GradedPowerMap` whose invertible module is `L`, such that `f^* A_1 ⟶ L` is
surjective and the associated morphism `r_{L, ψ} : X ⟶ Proj_S(A)` is an immersion. -/
def HasImmersionToRelativeProj (f : X ⟶ S) (L : X.Modules) : Prop :=
  ∃ (A : SheafGradedAlgebra.{u} S)
    (_ : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A)
    (P : GradedPowerMap A f) (_ : P.L = L) (h : Epi (degreeOneMap P)),
      IsImmersion (toRelativeProj P (coveringOpen_eq_top_of_epi P h))

/-- **The pullback of `𝒪_{𝐏(E)}(1)` along `r_{L, ψ} : X ⟶ 𝐏(E)` is `L`, and `r_{L, ψ}` exhibits
`L` as relatively very ample when it is an immersion.** Here `ψ` is a graded map for `Sym(E)`
whose degree-one values cover `X`. -/
theorem isRelativelyVeryAmple_of_isImmersion_toRelativeProj {E : S.Modules} [E.IsQuasicoherent]
    (P : GradedPowerMap (symAlgebra E) f)
    (h : ∀ x : X, ∃ (V : S.Opens) (_ : IsAffineOpen V)
      (a : Γ((symAlgebra E).piece ((1 : ℕ) : ℤ), V)), x ∈ P.nonvanishingOpenAt 1 V a)
    (himm : IsImmersion (toRelativeProj P (coveringOpen_eq_top_of_forall P h))) :
    IsRelativelyVeryAmple f P.L := by
  have h' : ∀ x : P.coveringOpen.toScheme, ∃ (V : S.Opens)
      (a : Γ((symAlgebra E).piece ((1 : ℕ) : ℤ), V)),
      P.coveringOpen.ι.base x ∈ P.nonvanishingOpenAt 1 V a := fun x => by
    obtain ⟨V, -, a, hx⟩ := h (P.coveringOpen.ι x)
    exact ⟨V, a, hx⟩
  exact isRelativelyVeryAmple_of_immersion f P.L E _ himm
    (toRelativeProj_comp_toBase P _)
    (Stacks.VeryAmpleGlue.pullbackTwistOneIso P (coveringOpen_eq_top_of_forall P h) h')

/-- **Stacks Tag 01VR, (3) implies (1).** Let `A` be generated in degree one and
`ψ : f^* A ⟶ ⨁_{n ≥ 0} L^{⊗ n}` with `f^* A_1 ⟶ L` surjective and `r_{L, ψ}` an immersion. Then
`L` is relatively very ample: precomposing `ψ` with the canonical map `Sym(A_1) ⟶ A`, surjective
in positive degrees over affine opens, gives a graded map for `Sym(A_1)` with the same degree-one
values, whose morphism `X ⟶ 𝐏(A_1)` has as charts the charts of `r_{L, ψ}` followed by closed
immersions. -/
theorem isRelativelyVeryAmple_of_hasImmersionToRelativeProj (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : HasImmersionToRelativeProj f L) :
    IsRelativelyVeryAmple f L := by
  obtain ⟨A, hgen, P, rfl, hepi, himm⟩ := h
  rw [isImmersion_toRelativeProj_iff] at himm
  let φ := Stacks.Tag01VMRelativeVeryAmple.canonicalSymHom A
  let Q := P.precomp φ
  have hQ : ∀ x : X, ∃ (V : S.Opens) (_ : IsAffineOpen V)
      (a : Γ((symAlgebra (A.piece 1)).piece ((1 : ℕ) : ℤ), V)),
      x ∈ Q.nonvanishingOpenAt 1 V a := by
    intro x
    obtain ⟨V, hV, b, hx⟩ := exists_mem_nonvanishingOpenAt_of_epi P x
    refine ⟨V, hV, Scheme.Modules.Hom.app
      (Scheme.Modules.symmetricAlgebraGen S (A.piece 1)) V b, ?_⟩
    change x ∈ Stacks.SectionPowerOpen.nonvanishingOpenOn _ _
      (P.value 1 V ((φ.app 1).app V _))
    rwa [Stacks.Tag01VMRelativeVeryAmple.canonicalSymHom_app_one_apply]
  have hsurj : ∀ V : S.Opens, IsAffineOpen V → ∀ n : ℕ, 0 < n →
      Function.Surjective (φ.sectionPieceHom V n) := by
    intro V hV n hn
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 1 := ⟨n - 1, by omega⟩
    exact AddMonoidHom.range_eq_top.mp
      (Stacks.Tag01VMRelativeVeryAmple.range_canonicalSymHom_sectionPieceHom_succ A hgen hV d)
  exact isRelativelyVeryAmple_of_isImmersion_toRelativeProj Q hQ
    ((isImmersion_toRelativeProj_iff Q _).mpr
      (isImmersion_globalMorphism_of_chartsAreImmersions Q (relativeProj (symAlgebra (A.piece 1)))
        (chartsAreImmersions_precomp P (relativeProj A) himm φ hsurj hQ)))

/-! ### Stacks Tag 01VR, clause (4) -/

section DirectImage

variable (f) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The identification `L ≅ L^{⊗ 1}` with the first tensor power of [Stacks, Tag 01CU]. -/
def tensorPowerOneIso :
    L ≅ Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ) :=
  (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).symm ≪≫
    Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1

variable [QuasiCompact f] [QuasiSeparated f]

/-- The direct image `f_* L` of an invertible module along a quasi-compact quasi-separated
morphism is quasi-coherent. -/
instance isQuasicoherent_pushforward_self :
    ((Scheme.Modules.pushforward f).obj L).IsQuasicoherent :=
  haveI := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  inferInstance

/-- **The graded map `ψ : f^* Sym(f_* L) ⟶ ⨁_{n ≥ 0} L^{⊗ n}` of clause (4) of Tag 01VR**, in
adjoint form: the extension to `Sym(f_* L)` of the identity `f_* L ⟶ f_* L`, followed by the
adjunction map `⨁_{n ≥ 0} f_* L^{⊗ n} ⟶ f_*(⨁_{n ≥ 0} L^{⊗ n})`. Its degree-one adjoint is the
canonical map `f^* f_* L ⟶ L`. -/
def directImageSymPowerMap :
    GradedPowerMap (symAlgebra ((Scheme.Modules.pushforward f).obj L)) f :=
  (Stacks.RelativeAmple.directImagePowerMap f L).precomp
    (symLift ((Scheme.Modules.pushforward f).obj L) (Stacks.RelativeAmple.directImageAlgebra f L)
      ((Scheme.Modules.pushforward f).map (tensorPowerOneIso L).hom))

/-- The invertible module of the graded map of clause (4) is `L`. -/
@[simp]
theorem directImageSymPowerMap_L : (directImageSymPowerMap f L).L = L := rfl

/-- **The degree-one values of the graded map of clause (4) are the sections of `L` themselves**:
the generator of a section `b` of `f_* L` over `V`, a section of `L` over `f⁻¹V`, is sent to `b`
read in `L^{⊗ 1}`. -/
theorem directImageSymPowerMap_value_gen (V : S.Opens)
    (b : Γ((Scheme.Modules.pushforward f).obj L, V)) :
    (directImageSymPowerMap f L).value 1 V
        (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
          ((Scheme.Modules.pushforward f).obj L)) V b) =
      (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ V) b := by
  change (Stacks.RelativeAmple.directImagePowerMap f L).value 1 V
      (((symLift ((Scheme.Modules.pushforward f).obj L)
        (Stacks.RelativeAmple.directImageAlgebra f L)
        ((Scheme.Modules.pushforward f).map (tensorPowerOneIso L).hom)).app 1).app V
        (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
          ((Scheme.Modules.pushforward f).obj L)) V b)) = _
  refine (congrArg (fun z => (Stacks.RelativeAmple.directImagePowerMap f L).value 1 V z)
    (symLift_app_one_symmetricAlgebraGen _ _ _ V b)).trans ?_
  change (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).inv.app (f ⁻¹ᵁ V)
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app (f ⁻¹ᵁ V)
        ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ V) b)) = _
  exact Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).symm (f ⁻¹ᵁ V) _

/-- A section of `L` over `f⁻¹V`, read as the degree-one value of the graded map of clause (4),
does not vanish where it does not vanish in `L`. -/
theorem mem_nonvanishingOpenAt_directImageSymPowerMap_iff (V : S.Opens)
    (b : Γ((Scheme.Modules.pushforward f).obj L, V)) (x : X) :
    x ∈ (directImageSymPowerMap f L).nonvanishingOpenAt 1 V
        (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
          ((Scheme.Modules.pushforward f).obj L)) V b) ↔
      x ∈ nonvanishingLocusOn L (f ⁻¹ᵁ V) b := by
  change x ∈ nonvanishingLocusOn _ (f ⁻¹ᵁ V) ((directImageSymPowerMap f L).value 1 V _) ↔ _
  rw [directImageSymPowerMap_value_gen]
  exact Set.ext_iff.mp (Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).symm (f ⁻¹ᵁ V) b) x

omit [Stacks.Ample.IsInvertibleModule X L] [QuasiCompact f] [QuasiSeparated f] in
/-- The adjoint of the identity of `f_* L` is the canonical map `f^* f_* L ⟶ L`. -/
theorem homEquiv_symm_id :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ L).symm
        (𝟙 ((Scheme.Modules.pushforward f).obj L)) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L := by
  rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The degree-one values of the graded map of clause (4) cover `X`, by sections over affine
opens of the base, when the canonical map `f^* f_* L ⟶ L` is surjective.** -/
theorem exists_mem_nonvanishingOpenAt_directImageSymPowerMap
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L)) (x : X) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V)
      (a : Γ((symAlgebra ((Scheme.Modules.pushforward f).obj L)).piece ((1 : ℕ) : ℤ), V)),
      x ∈ (directImageSymPowerMap f L).nonvanishingOpenAt 1 V a := by
  have : Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ L).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj L))) := by rwa [homEquiv_symm_id]
  obtain ⟨V, hV, b, hx⟩ := exists_mem_nonvanishingLocusOn_of_epi_adjoint f
    (𝟙 ((Scheme.Modules.pushforward f).obj L)) x
  exact ⟨V, hV, _, (mem_nonvanishingOpenAt_directImageSymPowerMap_iff f L V b x).mpr hx⟩

/-- `U(ψ) = X` for the graded map of clause (4) when `f^* f_* L ⟶ L` is surjective. -/
theorem coveringOpen_directImageSymPowerMap
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L)) :
    (directImageSymPowerMap f L).coveringOpen = ⊤ :=
  coveringOpen_eq_top_of_forall _ (exists_mem_nonvanishingOpenAt_directImageSymPowerMap f L h)

end DirectImage

/-- **Clause (4) of Stacks Tag 01VR.** `f` is quasi-separated, the canonical map
`f^* f_* L ⟶ L` is surjective and the associated morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` is an
immersion. Quasi-compactness of `f`, a standing hypothesis of the tag, is an instance argument;
quasi-separatedness, part of the clause, makes `f_* L` quasi-coherent (Tag 01LC). -/
def IsImmersionDirectImageBundle (f : X ⟶ S) [QuasiCompact f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  ∃ (_ : QuasiSeparated f)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L)),
      IsImmersion (toRelativeProj (directImageSymPowerMap f L)
        (coveringOpen_directImageSymPowerMap f L h))

variable (f) in
/-- **Stacks Tag 01VR, (4) implies (1).** The immersion `r_{L, ψ} : X ⟶ 𝐏(f_* L)` pulls
`𝒪_{𝐏(f_* L)}(1)` back to `L`. -/
theorem isRelativelyVeryAmple_of_isImmersionDirectImageBundle [QuasiCompact f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : IsImmersionDirectImageBundle f L) :
    IsRelativelyVeryAmple f L := by
  obtain ⟨_, hepi, himm⟩ := h
  exact isRelativelyVeryAmple_of_isImmersion_toRelativeProj (directImageSymPowerMap f L)
    (exists_mem_nonvanishingOpenAt_directImageSymPowerMap f L hepi) himm

variable (f) in
/-- **Stacks Tag 01VR, (4) implies (3)**, with `A = Sym(f_* L)`. -/
theorem hasImmersionToRelativeProj_of_isImmersionDirectImageBundle [QuasiCompact f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (h : IsImmersionDirectImageBundle f L) :
    HasImmersionToRelativeProj f L := by
  obtain ⟨_, hepi, himm⟩ := h
  refine ⟨_, Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top _,
    directImageSymPowerMap f L, rfl, epi_degreeOneMap_of_forall _ fun x => ?_, himm⟩
  obtain ⟨V, -, a, hx⟩ := exists_mem_nonvanishingOpenAt_directImageSymPowerMap f L hepi x
  exact ⟨V, a, hx⟩

end Stacks.Tag01VMVeryAmple

end
