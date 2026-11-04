module

public import StacksFrontier.RingTheory.Dualizing.Biduality
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# The derived homothety of a dualizing complex is invertible

Let `R` be a commutative ring and `ω` an object of `D(R)`. The *derived homothety* at `ω` is the
canonical morphism `R ⟶ RHom_R(ω, ω)`, obtained by transposing the left unitor along the
derived-Hom adjunction; invertibility of that morphism is one of the two hypotheses of the
biduality criterion `Dualizing.isIso_dualizingBidualityMor` of [stacks 0A7C].

The hypothesis is supposed to be supplied by the third field of `Dualizing.IsDualizingComplex`
([stacks 0A7B]), which says instead that the *chain-level* scalar homothety
`R[0] ⟶ Hom^•_R(I, I)` is a quasi-isomorphism for every bounded complex of injectives `I`
representing `ω`. Those two statements are not the same shape, and the identification between
them is what this file supplies.

`Dualizing.isIso_derivedHomothety_of_quasiIso` already reduces invertibility of the derived
homothety to a chain-level quasi-isomorphism, but the chain map it asks about is
`Φ ≫ ((λ ≫ f)_*)`, a composite of the morphism of [stacks 0A62] with postcomposition, and its
source complex must be K-flat while a bounded complex of injectives is not. The bridge is
therefore in two steps. First, the scalar homothety is identified with the `Φ`-composite
(`Dualizing.homothetyModel_precomp`): both send a scalar `a` to the cochain `a • f`, so the
identity holds componentwise once both sides are written as honest cochain composites. Second,
the source is moved from `I` to a K-flat complex: a K-flat resolution `f : L ⟶ I` of the
injective representative itself is a quasi-isomorphism, and precomposition with a
quasi-isomorphism is a quasi-isomorphism of Hom complexes when the target is K-injective
(`StacksDraft.DerivedHom.Construction.precomp_quasiIso_of_isKInjective`), so the `Φ`-composite out
of `L` is a quasi-isomorphism as soon as the scalar homothety of `I` is one.

The scalar homothety appears in three guises, differing only in which category the source lives
in: `Dualizing.homothety` is valued in universe-lifted abelian groups, which is the form
[stacks 0A7B] uses; `Dualizing.homothetyAddGrp` drops the lift; and `Dualizing.homothetyModel` is
`R`-module valued, which is the form `Stacks.HomComplex.TensorHomMap.precomp` acts on.
Quasi-isomorphy is the same condition for all three, because the universe lift and the forgetful
functor `ModuleCat R ⥤ AddCommGrpCat` both preserve homology and are faithful on the relevant
isomorphisms.

## Main definitions

* `Dualizing.homothetyModel` — the scalar homothety `R[0] ⟶ Hom^•_R(I, I)` in complexes of
  `R`-modules.
* `Dualizing.homothetyAddGrp` — the same map in complexes of abelian groups.

## Main results

* `Dualizing.quasiIso_homothetyModel_iff` and `Dualizing.quasiIso_homothetyAddGrp_iff` — the three
  guises of the scalar homothety are quasi-isomorphisms together.
* `Dualizing.homothetyModel_precomp` — the scalar homothety followed by precomposition with
  `f : P ⟶ I` is the `Φ`-composite of [stacks 0A62] out of `P`.
* `Dualizing.isIso_derivedHomothety_of_injectiveRepresentative` — the derived homothety at `ω` is
  invertible as soon as the scalar homothety of one bounded-below complex of injectives
  representing `ω` is a quasi-isomorphism.
* `Dualizing.isIso_derivedHomothety_of_isDualizingComplex` — hence it is invertible for a
  dualizing complex.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

universe w

namespace Dualizing

variable {R : Type w} [CommRing R]

/-! ### The scalar homothety in complexes of modules and of abelian groups -/

/-- The scalar homothety `R[0] ⟶ Hom^•_R(I, I)`, as a morphism of complexes of `R`-modules: in
degree zero it sends `a` to the cochain `a • 𝟙 I`, and all other degrees are zero. -/
def homothetyModel (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R) ⟶
      CochainComplex.HomComplexR R I I :=
  mkHomFromSingle
    (ModuleCat.ofHom
      { toFun := fun a ↦ a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)
        map_add' _ _ := by simp [add_smul]
        map_smul' _ _ := by simp [smul_smul] })
    (fun k hk ↦ by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change CochainComplex.HomComplex.δ 0 1
        (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
      simp)

/-- In degree zero, `Dualizing.homothetyModel I` sends `a` to the cochain `a • 𝟙 I`. -/
@[simp]
theorem homothetyModel_f_zero_apply (I : CochainComplex (ModuleCat.{w} R) ℤ)
    (a : ((CochainComplex.singleFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).X 0) :
    ((homothetyModel I).f 0).hom a =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) :=
  rfl

/-- The scalar homothety `R[0] ⟶ Hom^•(I, I)` in complexes of abelian groups: the image of
`Dualizing.homothetyModel` under the forgetful functor, before the universe lift that
`Dualizing.homothety` carries. -/
def homothetyAddGrp (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    (CochainComplex.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of R) ⟶
      CochainComplex.HomComplex I I :=
  mkHomFromSingle
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦ a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)
        map_zero' := by ext; simp
        map_add' _ _ := by ext; simp [add_smul] })
    (fun k hk ↦ by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      ext a
      change CochainComplex.HomComplex.δ 0 1
        (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
      simp)

/-- In degree zero, `Dualizing.homothetyAddGrp I` sends `a` to the cochain `a • 𝟙 I`. -/
@[simp]
theorem homothetyAddGrp_f_zero_apply (I : CochainComplex (ModuleCat.{w} R) ℤ)
    (a : ((CochainComplex.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of R)).X 0) :
    ((homothetyAddGrp I).f 0).hom a =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (AddCommGrpCat.of R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) :=
  rfl

/-- Quasi-isomorphy of a morphism `g` is detected after applying a homology-preserving functor
reflecting isomorphisms, when `g` factors through a quasi-isomorphism into the image. -/
private theorem quasiIso_iff_of_comp_map {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms]
    {K L : CochainComplex C ℤ} {A : CochainComplex D ℤ} (φ : K ⟶ L)
    (s : A ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) [QuasiIso s]
    (g : A ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (hg : s ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ = g) :
    QuasiIso φ ↔ QuasiIso g := by
  rw [← hg, quasiIso_iff_comp_left, quasiIso_map_iff_of_preservesHomology]

/-- Dropping the universe lift does not change quasi-isomorphy of the scalar homothety: the lift
of `Dualizing.homothetyAddGrp` is `Dualizing.homothety` up to the canonical identification of the
lifted single complex, and the lift preserves homology. -/
theorem quasiIso_homothetyAddGrp_iff (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    QuasiIso (homothetyAddGrp I) ↔ QuasiIso (homothety I) := by
  refine quasiIso_iff_of_comp_map AddCommGrpCat.uliftFunctor.{w, w} _
    (((Functor.mapCochainComplexSingleFunctor _ 0).app (AddCommGrpCat.of R)).inv) _ ?_
  apply from_single_hom_ext
  ext a
  rfl

/-- Forgetting the module structure does not change quasi-isomorphy of the scalar homothety. -/
theorem quasiIso_homothetyModel_iff (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    QuasiIso (homothetyModel I) ↔ QuasiIso (homothety I) := by
  rw [← quasiIso_homothetyAddGrp_iff]
  refine quasiIso_iff_of_comp_map (forget₂ (ModuleCat.{w} R) AddCommGrpCat) _
    (((Functor.mapCochainComplexSingleFunctor _ 0).app (ModuleCat.of R R)).inv) _ ?_
  apply from_single_hom_ext
  ext a
  rfl

/-! ### Identification with the morphism of [stacks 0A62] -/

/-- The left unitor of the monoidal structure on cochain complexes, read on an element of the
tensor product with the unit: it is scalar multiplication through the identification of the
degree-zero term of the unit complex with `R`. -/
theorem singleUnitorTensor_apply (I : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)
    (a : (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X 0) (x : I.X n) :
    ((λ_ I).hom.f n).hom ((ιTensorObj _ I 0 n n (zero_add n)).hom (a ⊗ₜ[R] x)) =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).hom.hom a) • x := by
  have h : (λ_ I).inv.f n = (λ_ (I.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).inv ▷ I.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) I 0 n n (zero_add n) :=
    leftUnitor'_inv I n
  have hh : ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) I 0 n n (zero_add n) ≫
        (λ_ I).hom.f n =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).hom ▷ I.X n) ≫
        (λ_ (I.X n)).hom := by
    apply (cancel_epi ((λ_ (I.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).inv ▷ I.X n))).mp
    simp only [Category.assoc]
    rw [← reassoc_of% h]
    simp
  exact ConcreteCategory.congr_hom hh (a ⊗ₜ[R] x)

/-- The scalar homothety of `I` followed by precomposition with `f : P ⟶ I` is the composite of
the morphism `Φ` of [stacks 0A62] with postcomposition by `(λ_ P).hom ≫ f`: both send a scalar
`a` to the cochain `a • f`. -/
theorem homothetyModel_precomp {P I : CochainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ I) :
    homothetyModel I ≫ Stacks.HomComplex.TensorHomMap.precomp R P I I f =
      Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) P ≫
        Stacks.HomComplex.TensorHomMap.postcomp R P ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⊗ P)
          I
          ((λ_ P).hom ≫ f) := by
  apply from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  -- Name both sides as composites of cochains before touching their components: the carrier of
  -- `(HomComplexR R P I).X 0` is only definitionally `Cochain P I 0`, and the component lemmas
  -- below do not match through that.
  show (CochainComplex.HomComplex.Cochain.ofHom f).comp
      (((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) (zero_add 0) =
    (Stacks.HomComplex.TensorHomMap.Phiv R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) P 0 a).comp
      (CochainComplex.HomComplex.Cochain.ofHom ((λ_ P).hom ≫ f)) (add_zero 0)
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ (zero_add 0) n n n (by omega) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero 0) n n n (by omega) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_v, Stacks.HomComplex.TensorHomMap.Phiv_v]
  simp only [ModuleCat.comp_apply, comp_f, Stacks.HomComplex.TensorHomMap.tmulLeft_apply]
  rw [CochainComplex.HomComplex.Cochain.smul_v, CochainComplex.HomComplex.Cochain.ofHom_v,
    singleUnitorTensor_apply]
  exact ((f.f n).hom.map_smul _ _).symm

/-! ### Invertibility of the derived homothety -/

/-- **The derived homothety of [stacks 0A7C] is invertible as soon as the scalar homothety of one
injective representative is a quasi-isomorphism.** If `I` is a bounded-below complex of
injective `R`-modules representing `ω` whose scalar homothety `R[0] ⟶ Hom^•_R(I, I)` is a
quasi-isomorphism, then the derived homothety `R ⟶ RHom_R(ω, ω)` is an isomorphism. -/
theorem isIso_derivedHomothety_of_injectiveRepresentative
    (d : StacksDraft.DerivedHom.DerivedHomData R) (ω : DerivedCategory (ModuleCat.{w} R))
    (I : CochainComplex (ModuleCat.{w} R) ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ i : ℤ, Injective (I.X i)] (e : DerivedCategory.Q.obj I ≅ ω)
    (hI : QuasiIso (homothety I)) :
    IsIso (derivedHomothety d.toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex R)))
      d.tensorUnitLeft ω) := by
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  obtain ⟨L, g, hL, -, hg, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{w, w} I
  have : IsIso (DerivedCategory.Q.map g) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  refine isIso_derivedHomothety_of_quasiIso d ω L I hL g (asIso (DerivedCategory.Q.map g) ≪≫ e)
    e (by simp) ?_
  have hprecomp : QuasiIso (Stacks.HomComplex.TensorHomMap.precomp R L I I g) :=
    StacksDraft.DerivedHom.Construction.precomp_quasiIso_of_isKInjective g
  have : QuasiIso (homothetyModel I) := (quasiIso_homothetyModel_iff I).2 hI
  rw [← homothetyModel_precomp g]
  exact quasiIso_comp (homothetyModel I) (Stacks.HomComplex.TensorHomMap.precomp R L I I g)

/-- **The derived homothety of a dualizing complex is invertible.** For a dualizing complex `ω`
over a Noetherian ring `R` ([stacks 0A7B]), the derived homothety `R ⟶ RHom_R(ω, ω)` is an
isomorphism. This is the hypothesis `hone` of the biduality criterion
`Dualizing.isIso_dualizingBidualityMor` of [stacks 0A7C]. -/
theorem isIso_derivedHomothety_of_isDualizingComplex [IsNoetherianRing R]
    (d : StacksDraft.DerivedHom.DerivedHomData R) (ω : DerivedCategory (ModuleCat.{w} R))
    (hω : IsDualizingComplex ω) :
    IsIso (derivedHomothety d.toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex R)))
      d.tensorUnitLeft ω) := by
  obtain ⟨a, b, I, hge, hle, hinj, ⟨e⟩⟩ := hω.finiteInjectiveDimension
  have : I.IsStrictlyGE a := hge
  have : ∀ i : ℤ, Injective (I.X i) := hinj
  exact isIso_derivedHomothety_of_injectiveRepresentative d ω I a e.symm
    (hω.homothetyQuasiIso I ⟨e.symm⟩ hinj ⟨a, b, hge, hle⟩)

end Dualizing

end
