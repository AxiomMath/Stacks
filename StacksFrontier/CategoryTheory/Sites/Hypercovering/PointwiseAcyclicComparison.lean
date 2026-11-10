module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparisonBoundedBelow
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The hypercovering comparison at a sheaf acyclic on the members

Let `K` be a hypercovering of an object `U` of a site and let `F` be an abelian sheaf whose
higher cohomology vanishes on every member `U_i` of `K`.  Then the comparison map
`s(F(K)) ⟶ RΓ(U, F)` of [Stacks, Tag 01GY] is an *isomorphism* in `D⁺(Ab)`, and the induced maps
`Ȟ^i(K, F) ⟶ H^i(U, F)` are isomorphisms in every degree.  This is the degeneration input to the
proof of [Stacks, Tag 01XN]: the hypercovering produced there has affine members, on which a
quasi-coherent sheaf is acyclic.

## Main results

* `CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution`:
  an additive functor
  carries a bounded below injective resolution of a right acyclic object to a
  quasi-isomorphism.
* `quasiIso_hypercoverRow_map`: **the rows of the hypercover bicomplex of a resolution are
  resolutions**, which is where the acyclicity hypothesis enters.
* `quasiIso_total_map_of_bounded_flip`: Weibel's acyclic assembly lemma for double complexes
  bounded below, with the hypothesis on the rows rather than on the columns.
* `quasiIso_hypercoverTotalCochainFunctor_map`: `Tot(s(-(K)))` carries the resolution to a
  quasi-isomorphism.
* `isIso_hypercoverRightDerivedUnit_app_single`: `F[0]` computes `RΘ`.
* `isIso_hypercoverComparisonMap_app` and `isIso_hypercoverCohomologyComparison_app`: the
  comparison map and the maps it induces on cohomology are isomorphisms at `F`.

## Implementation notes

The comparison map of [Stacks, Tag 01GY] is built in
`StacksFrontier/CategoryTheory/Sites/Hypercovering/DerivedComparisonBoundedBelow.lean` out of three
factors, two of which are isomorphisms for every hypercovering and every sheaf: the
identification of `s(F(K))` with `Θ(F[0])` and the comparison `RΓ(U, -) ⟶ RΘ`, which is
invertible because both functors are right derived.  So the whole content here is that the
remaining factor, the *unit* `Θ ⟶ Qh ⋙ RΘ` of the right derived functor of `Θ`, is invertible at
`F[0]` — that is, that `F[0]` is right acyclic for `Θ`.

That is proved by naturality of the unit along a quasi-isomorphism `φ : F[0] ⟶ I^•` to a bounded
below complex of injective sheaves.  The unit is invertible at `I^•` because `RΘ` is a right
derived functor and `I^•` has injective terms, and `RΘ(Qh(φ))` is invertible because `Qh(φ)` is;
so the unit is invertible at `F[0]` exactly when `Θ(φ)` is, i.e. when `Tot(s(I^•(K)))` receives a
quasi-isomorphism from `Tot(s(F[0](K)))`.

For that last statement the double complex has to be read along its *rows*: the row in Čech
degree `n` of the hypercover bicomplex of `E` is `E` evaluated on the members of `K_n`, so the
row of `φ` is the product over `i` of the sections of `φ` on `U_i`.  Each factor is a
quasi-isomorphism because `F` is acyclic on `U_i`, quasi-isomorphy in a category of functors on a
discrete category is quasi-isomorphy in each component, and products are exact in abelian groups;
Weibel's acyclic assembly lemma then passes from the rows to the total complexes, the row form
being obtained from the column form by `HomologicalComplex₂.totalFlipIso`.

The hypothesis is stated as the vanishing of the higher right derived functors of sections on the
members, which is the source's `H^q(U_i, F) = 0` for `q > 0`; `CategoryTheory.Functor.rightAcyclic`
is the equivalent form the proof uses, the two being identified by
`Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat`.

The statement carries no Stacks tag: the source has no separate lemma for it, deriving it inside
the proof of [Stacks, Tag 01XN] from the spectral sequence of [Stacks, Tag 01GY].  It is also not
a strengthening of [Stacks, Tag 09A2]
(`Stacks.CategoryTheory.Hypercovering.derivedSectionsIsoHypercoverTotalComplex`), whose hypothesis
is weak contractibility of the members — a condition on the site, not on the coefficients, and one
which applies to every bounded below complex rather than to a single sheaf.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape Simplicial

/-- A quasi-isomorphism of complexes becomes invertible in `D⁺`, viewed as a morphism of `K⁺`. -/
private lemma isIso_plusQh_map_homMk_quotient_map {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {X Y : CochainComplex A ℤ} (φ : X ⟶ Y)
    [QuasiIso φ]
    (hX : HomotopyCategory.plus A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X))
    (hY : HomotopyCategory.plus A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) :
    IsIso (DerivedCategory.Plus.Qh.map (ObjectProperty.homMk
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ) :
        (⟨_, hX⟩ : HomotopyCategory.Plus A) ⟶ ⟨_, hY⟩)) := by
  suffices IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (ObjectProperty.homMk
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ) :
        (⟨_, hX⟩ : HomotopyCategory.Plus A) ⟶ ⟨_, hY⟩))) from
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) φ).2 inferInstance

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **An additive functor carries a bounded below injective resolution of a right acyclic object
to a quasi-isomorphism.**

The unit `α : G ⟶ Qh ⋙ RG` of the right derived functor is invertible at `I^•`, because `I^•` has
injective terms, and at `M[0]`, because `M` is right acyclic; and `RG(Qh(φ))` is invertible
because `φ` is a quasi-isomorphism.  Naturality of `α` along `φ` then makes `G(φ)` invertible in
`D⁺(B)`, hence a quasi-isomorphism. -/
lemma quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution (G : A ⥤ B) [G.Additive]
    {M : A} {I : CochainComplex A ℤ} (n : ℤ) [I.IsStrictlyGE n]
    (hinj : ∀ p : ℤ, Injective (I.X p))
    (φ : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M ⟶ I) [QuasiIso φ]
    (hM : G.rightAcyclic M) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  let Y : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
      (HomotopyCategory.plus_quotient_obj_iff I).2 ⟨n, inferInstance⟩⟩
  let a : (HomotopyCategory.Plus.singleFunctor A 0).obj M ⟶ Y :=
    ObjectProperty.homMk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ)
  have hYinj : ∀ i : ℤ, Injective (Y.obj.as.X i) := hinj
  have h1 : IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) := hM
  have h2 : IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app Y) := inferInstance
  have h3 : IsIso (DerivedCategory.Plus.Qh.map a) := isIso_plusQh_map_homMk_quotient_map φ _ _
  have h4 : IsIso ((DerivedCategory.Plus.Qh ⋙
      (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).map a) := by
    change IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).map
        (DerivedCategory.Plus.Qh.map a))
    infer_instance
  have h5 : IsIso ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map a) := by
    have hcomp : IsIso ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map a ≫
        ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app Y) := by
      rw [((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).naturality a]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app Y)
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  refine (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso B)) φ).1 ?_
  exact inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map a)))

end CategoryTheory.Functor

universe w v u

namespace StacksDraft.TotalComplexQuasiIso

universe v' u'

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- **Weibel's acyclic assembly lemma on the rows, for double complexes bounded below**: a
morphism of double complexes vanishing in second degrees `< b` and first degrees `< a` which is a
quasi-isomorphism on every *row* is a quasi-isomorphism on total complexes.

The column form is `Stacks.CategoryTheory.Hypercovering.quasiIso_total_map_of_bounded`; it is
applied here to the flipped morphism, where the two bounds exchange roles, and transported back
along `totalFlipIso_naturality`. -/
lemma quasiIso_total_map_of_bounded_flip
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (a b : ℤ)
    (hq : ∀ p q, q < b → IsZero ((Z.X p).X q))
    (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < b → IsZero ((Z'.X p).X q))
    (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ q, QuasiIso ((flipHom f).f q)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  have hflip : QuasiIso (HomologicalComplex₂.total.map (flipHom f) (up ℤ)) := by
    refine Stacks.CategoryTheory.Hypercovering.quasiIso_total_map_of_bounded (flipHom f) b a
      (fun p q hqa ↦ (HomologicalComplex.eval A (up ℤ) p).map_isZero (hp q hqa))
      (fun p hpb ↦ Stacks.CategoryTheory.Hypercovering.isZero_complex_of_components _
        (fun q ↦ hq q p hpb))
      (fun p q hqa ↦ (HomologicalComplex.eval A (up ℤ) p).map_isZero (hp' q hqa))
      (fun p hpb ↦ Stacks.CategoryTheory.Hypercovering.isZero_complex_of_components _
        (fun q ↦ hq' q p hpb)) hf
  have h1 : QuasiIso (HomologicalComplex₂.total.map (flipHom f) (up ℤ) ≫
      (Z'.totalFlipIso (up ℤ)).hom) := quasiIso_comp _ _
  rw [totalFlipIso_naturality f] at h1
  exact quasiIso_of_comp_left (Z.totalFlipIso (up ℤ)).hom _

end StacksDraft.TotalComplexQuasiIso

namespace Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (J : Pretopology C) (U : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over U)))

/-- The row of the hypercover bicomplex in Čech degree `n`: an abelian sheaf evaluated on the
members of `K_n`, with the alternating cofaces of the simplicial object forgotten. -/
def hypercoverRowFunctor (n : ℤ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w} :=
  hypercoverCochainIntFunctor J U K ⋙ HomologicalComplex.eval _ (up ℤ) n

/-- The row of the hypercover bicomplex in Čech degree `n` is an additive functor. -/
instance hypercoverRowFunctor_additive (n : ℤ) : (hypercoverRowFunctor J U K n).Additive := by
  dsimp only [hypercoverRowFunctor]
  infer_instance

/-- The functor of sections on the members of `T` is additive. -/
instance familySectionsFunctor_additive (T : FormalCoproduct.{w} (Over U)) :
    (familySectionsFunctor J U T).Additive := by
  dsimp only [familySectionsFunctor]
  infer_instance

/-- **The row of the hypercover bicomplex in Čech degree `n` is the product of the sections on
the members of `K_n`**, naturally in the abelian sheaf: the degreewise description
`hypercoverDegreeIso` of `s(-(K))`, read through the extension by zero from `ℕ` to `ℤ`. -/
def hypercoverRowFunctorIso (n : ℕ) :
    hypercoverRowFunctor J U K (n : ℤ) ≅ familySectionsFunctor J U (K.obj (op ⦋n⦌)) ⋙ lim :=
  Functor.isoWhiskerLeft (hypercoverCochainNatFunctor J U K)
      (embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{max u v w} (i := n) rfl) ≪≫
    hypercoverDegreeIso J U K n

section Rows

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]
  {F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}}
  {I : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ}

/-- **The rows of the hypercover bicomplex of an injective resolution are resolutions.**

In negative Čech degree the row vanishes.  In Čech degree `n` it is, by
`hypercoverRowFunctorIso`, the product over the members of `K_n` of the sections functors:
quasi-isomorphy of a morphism of complexes of functors on a discrete category is quasi-isomorphy
in each component, where it holds because `F` is acyclic on that member, and the product functor
is exact because abelian groups satisfy AB4*. -/
lemma quasiIso_hypercoverRow_map (m : ℤ) [I.IsStrictlyGE m]
    (hinj : ∀ p : ℤ, Injective (I.X p))
    (φ : (HomologicalComplex.single _ (up ℤ) 0).obj F ⟶ I) [QuasiIso φ]
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left).rightAcyclic F)
    (n : ℤ) :
    QuasiIso (((hypercoverRowFunctor J U K n).mapHomologicalComplex (up ℤ)).map φ) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let G := familySectionsFunctor J U (K.obj (op ⦋n⦌))
    have hdisc : QuasiIso ((G.mapHomologicalComplex (up ℤ)).map φ) := by
      rw [HomologicalComplex.quasiIso_iff_evaluation]
      rintro ⟨i⟩
      exact Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution
        (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left) m hinj φ (hac n i)
    let : AB4StarOfSize.{w} AddCommGrpCat.{max u v w} := AB4StarOfSize_shrink _
    let L : (Discrete (K.obj (op ⦋n⦌)).I ⥤ AddCommGrpCat.{max u v w}) ⥤
      AddCommGrpCat.{max u v w} := lim
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    have : PreservesFiniteLimits L := inferInstance
    have : PreservesFiniteColimits L := inferInstance
    have : L.PreservesHomology := inferInstance
    have hlim : QuasiIso (((G ⋙ L).mapHomologicalComplex (up ℤ)).map φ) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology
        ((G.mapHomologicalComplex (up ℤ)).map φ) L
    have harr : QuasiIso (((G ⋙ L).mapHomologicalComplex (up ℤ)).map (Arrow.mk φ).hom) := hlim
    exact quasiIso_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso
      (NatIso.mapHomologicalComplex (hypercoverRowFunctorIso J U K n).symm (up ℤ))
      (Arrow.mk φ))
  · have hz : ∀ G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w},
        IsZero ((hypercoverRowFunctor J U K n).obj G) := fun G ↦
      CochainComplex.isZero_of_isStrictlyGE
        (((hypercoverCochainNatFunctor J U K).obj G).extend embeddingUpNat) 0 n (by omega)
    have h1 : IsZero (((hypercoverRowFunctor J U K n).mapHomologicalComplex (up ℤ)).obj
        ((HomologicalComplex.single _ (up ℤ) 0).obj F)) :=
      isZero_complex_of_components _ (fun p ↦ hz _)
    have h2 : IsZero (((hypercoverRowFunctor J U K n).mapHomologicalComplex (up ℤ)).obj I) :=
      isZero_complex_of_components _ (fun p ↦ hz _)
    have : IsIso (((hypercoverRowFunctor J U K n).mapHomologicalComplex (up ℤ)).map φ) :=
      h1.isIso h2 _
    exact quasiIso_of_isIso _

/-- **The hypercover total complex carries an injective resolution of an acyclic sheaf to a
quasi-isomorphism.**  The hypothesis of
`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_bounded_flip` on the rows is
`quasiIso_hypercoverRow_map`; the two bounds are the Čech degree, bounded below by `0`, and the
degree in the complex, bounded below by `min 0 m`. -/
lemma quasiIso_hypercoverTotalCochainFunctor_map (m : ℤ) [I.IsStrictlyGE m]
    (hinj : ∀ p : ℤ, Injective (I.X p))
    (φ : (HomologicalComplex.single _ (up ℤ) 0).obj F ⟶ I) [QuasiIso φ]
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left).rightAcyclic F) :
    QuasiIso ((hypercoverTotalCochainFunctor J U K).map φ) := by
  have hI : I.IsStrictlyGE (min 0 m) := I.isStrictlyGE_of_ge (min 0 m) m (by omega)
  have hF : CochainComplex.IsStrictlyGE ((HomologicalComplex.single
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ) 0).obj F) (min 0 m) :=
    CochainComplex.isStrictlyGE_of_ge _ (min 0 m) 0 (by omega)
  rw [hypercoverTotalCochainFunctor_map]
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_bounded_flip
    ((hypercoverBicomplexFunctor J U K).map φ) (min 0 m) 0
    (fun p q hq ↦ CochainComplex.isZero_of_isStrictlyGE
      (((hypercoverCochainNatFunctor J U K).obj
        (((HomologicalComplex.single _ (up ℤ) 0).obj F).X p)).extend embeddingUpNat) 0 q hq)
    (fun p hp ↦ (hypercoverCochainIntFunctor J U K).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE _ (min 0 m) p hp))
    (fun p q hq ↦ CochainComplex.isZero_of_isStrictlyGE
      (((hypercoverCochainNatFunctor J U K).obj (I.X p)).extend embeddingUpNat) 0 q hq)
    (fun p hp ↦ (hypercoverCochainIntFunctor J U K).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE _ (min 0 m) p hp))
    (fun q ↦ quasiIso_hypercoverRow_map J U K m hinj φ hac q)

end Rows

section Acyclic

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]

/-- Sections of abelian sheaves on an object of the site preserve finite limits: the inclusion of
sheaves into presheaves and evaluation both do. -/
instance preservesFiniteLimits_sheafSectionsFunctor (V : C) :
    PreservesFiniteLimits (sheafSectionsFunctor.{w} J V) := by
  dsimp only [sheafSectionsFunctor]
  infer_instance

omit [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **A sheaf acyclic on the members of a hypercovering is right acyclic for `Θ`**: the unit
`Θ ⟶ Qh ⋙ RΘ` of the right derived functor of the hypercover total complex is invertible at
`F[0]`.

The unit is invertible at a bounded below complex of injective sheaves because `RΘ` is a right
derived functor, and `RΘ(Qh(φ))` is invertible because `φ` is a quasi-isomorphism; so naturality
of the unit along `φ` reduces the claim to the invertibility of `Θ(φ)`, which is
`quasiIso_hypercoverTotalCochainFunctor_map`. -/
lemma isIso_hypercoverRightDerivedUnit_app_single
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left).rightAcyclic F) :
    IsIso ((hypercoverRightDerivedUnit J U K).app
      ((HomotopyCategory.Plus.singleFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F)) := by
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    (⟨(HomologicalComplex.single
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ) 0).obj F,
      ⟨0, inferInstance⟩⟩ : CochainComplex.Plus _) 0
  set Ic := ((InjectiveObject.ι _).mapCochainComplexPlus.obj L).obj with hIc
  have hIcGE : Ic.IsStrictlyGE 0 := by
    rw [hIc]
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapHomologicalComplex (up ℤ)).obj L.obj) 0
    have : L.obj.IsStrictlyGE 0 := hL
    infer_instance
  have hIcInj : ∀ p : ℤ, Injective (Ic.X p) := fun p ↦ (L.obj.X p).property
  have hφ : QuasiIso i.hom := hi
  have htot : QuasiIso ((hypercoverTotalCochainFunctor J U K).map i.hom) :=
    quasiIso_hypercoverTotalCochainFunctor_map J U K 0 hIcInj i.hom hac
  let Y : HomotopyCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :=
    ⟨(HomotopyCategory.quotient _ (up ℤ)).obj Ic,
      (HomotopyCategory.plus_quotient_obj_iff Ic).2 ⟨0, hIcGE⟩⟩
  let a : (HomotopyCategory.Plus.singleFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F ⟶ Y :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ (up ℤ)).map i.hom)
  have hYinj : ∀ p : ℤ, Injective (Y.obj.as.X p) := hIcInj
  have h2 : IsIso ((hypercoverRightDerivedUnit J U K).app Y) := inferInstance
  have h3 : IsIso (DerivedCategory.Plus.Qh.map a) :=
    isIso_plusQh_map_homMk_quotient_map i.hom _ _
  have h4 : IsIso ((DerivedCategory.Plus.Qh ⋙ hypercoverRightDerived J U K).map a) := by
    change IsIso ((hypercoverRightDerived J U K).map (DerivedCategory.Plus.Qh.map a))
    infer_instance
  have hmem : HomotopyCategory.Plus.quasiIso AddCommGrpCat.{max u v w}
      ((hypercoverTotalPlusFunctor J U K).map a) := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    change HomotopyCategory.quasiIso _ _
      ((HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ)).map
        ((hypercoverTotalCochainFunctor J U K).map i.hom))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact htot
  have h5 : IsIso ((hypercoverTotalDerivedFunctor J U K).map a) := by
    change IsIso (DerivedCategory.Plus.Qh.map ((hypercoverTotalPlusFunctor J U K).map a))
    exact Localization.inverts DerivedCategory.Plus.Qh _ _ hmem
  have hcomp : IsIso ((hypercoverRightDerivedUnit J U K).app
      ((HomotopyCategory.Plus.singleFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F) ≫
      (DerivedCategory.Plus.Qh ⋙ hypercoverRightDerived J U K).map a) := by
    rw [← (hypercoverRightDerivedUnit J U K).naturality a]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Qh ⋙ hypercoverRightDerived J U K).map a)

/-- **The comparison map of [Stacks, Tag 01GY] is an isomorphism at a sheaf acyclic on the
members of the hypercovering**, with the hypothesis in the form
`CategoryTheory.Functor.rightAcyclic`. -/
lemma isIso_hypercoverComparisonMap_app_of_rightAcyclic (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left).rightAcyclic F) :
    IsIso ((hypercoverComparisonMap J U K hK).app F) := by
  have hunit := isIso_hypercoverRightDerivedUnit_app_single J U K F hac
  have hcmp : IsIso (derivedSectionsToHypercoverRightDerived J U K hK) :=
    NatIso.isIso_of_isIso_app _
  have h : IsIso ((hypercoverRightDerivedToDerivedSections J U K hK).app
      ((HomotopyCategory.Plus.singleFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F)) := by
    have e : (hypercoverRightDerivedToDerivedSections J U K hK).app
          ((HomotopyCategory.Plus.singleFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F) =
        (hypercoverRightDerivedUnit J U K).app
            ((HomotopyCategory.Plus.singleFunctor
              (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F) ≫
          (inv (derivedSectionsToHypercoverRightDerived J U K hK)).app
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor
              (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F)) := rfl
    rw [e]
    infer_instance
  have e : (hypercoverComparisonMap J U K hK).app F =
      (hypercoverDerivedSingleIso J U K).hom.app F ≫
        ((hypercoverRightDerivedToDerivedSections J U K hK).app
            ((HomotopyCategory.Plus.singleFunctor
              (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).obj F) ≫
          (sheafSectionsFunctor J U).rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh
              (A := Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).inv.app F)) := rfl
  have hA : IsIso ((hypercoverDerivedSingleIso J U K).hom.app F) := inferInstance
  have hC : IsIso ((sheafSectionsFunctor J U).rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh
        (A := Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).inv.app F)) := inferInstance
  rw [e]
  exact IsIso.comp_isIso' hA (IsIso.comp_isIso' h hC)

/-- **The comparison map `s(F(K)) ⟶ RΓ(U, F)` of [Stacks, Tag 01GY] is an isomorphism as soon as
`H^q(U_i, F) = 0` for every `q > 0` and every member `U_i` of the hypercovering `K`.**

The hypothesis is pointwise acyclicity of the coefficient sheaf on the objects of the site
appearing in `K`; no condition on the site and no condition on `F` beyond that is imposed. -/
theorem isIso_hypercoverComparisonMap_app (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I) (q : ℕ), 0 < q →
      IsZero ((((sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left)).rightDerived q).obj
        F)) :
    IsIso ((hypercoverComparisonMap J U K hK).app F) :=
  isIso_hypercoverComparisonMap_app_of_rightAcyclic J U K hK F (fun n i ↦
    (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
      (sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left) F).2 (hac n i))

/-- **The maps `Ȟ^i(K, F) ⟶ H^i(U, F)` of [Stacks, Tag 01GY] are isomorphisms in every degree as
soon as `H^q(U_i, F) = 0` for every `q > 0` and every member `U_i` of the hypercovering `K`.**
They are the comparison map of `isIso_hypercoverComparisonMap_app` read in cohomology. -/
theorem isIso_hypercoverCohomologyComparison_app (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (hac : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I) (q : ℕ), 0 < q →
      IsZero ((((sheafSectionsFunctor.{w} J ((K.obj (op ⦋n⦌)).obj i).left)).rightDerived q).obj
        F))
    (i : ℤ) :
    IsIso ((hypercoverCohomologyComparison J U K hK i).app F) := by
  have := isIso_hypercoverComparisonMap_app J U K hK F hac
  dsimp only [hypercoverCohomologyComparison, Functor.whiskerRight_app]
  infer_instance

end Acyclic

end Stacks.CategoryTheory.Hypercovering

end
