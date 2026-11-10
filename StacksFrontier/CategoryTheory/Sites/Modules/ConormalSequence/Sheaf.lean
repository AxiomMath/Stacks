module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence.Presheaf

/-!
# The conormal sequence of a quotient of sheaves of rings

Let `R ⟶ A ⟶ B` be morphisms of presheaves of commutative rings on a site `(C, J)`, with
`A ⟶ B` locally surjective and `R`, `A`, `B` sheaves. Writing `I` for the kernel of `A ⟶ B`,
this file constructs the canonical sequence of sheaves of `B`-modules

`I/I² ⟶ B ⊗[A] Ω[A/R] ⟶ Ω[B/R] ⟶ 0`

proves that it is exact at the middle term, and proves that its right-hand map is an
epimorphism.

The three terms are the sheafifications along the locally bijective map `Q ⟶ B` from the image
presheaf `Q(U) = A(U)/I(U)` of the objectwise conormal sequence over `Q` constructed in
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence.Presheaf`; the right-hand term is
`Ω[B/R]` because `Q` sheafifies to `B`. The file starts with the compatibility of the objectwise
change-of-presentation maps with composition, which the sheaf-level maps inherit.

## Main definitions

* `Stacks.Sites.Conormal.liftModules`: the objectwise universe lift of presheaves of modules.
* `Stacks.Sites.Conormal.conormalSequence`: the conormal sequence of sheaves of `B`-modules.
* `Stacks.Sites.Conormal.conormalClass`, `Stacks.Sites.Conormal.tensorDifferential` and
  `Stacks.Sites.Conormal.quotientDifferential`: the local sections `f mod I²`, `1 ⊗ d f` and
  `d (f mod I)` of the three terms.
* `Stacks.Sites.Conormal.sheafifyLiftDesc`: the morphism of sheaves of modules out of the
  sheafification of a presheaf of modules classifying a compatible family of maps on sections.
* `Stacks.Sites.Conormal.conormalSheafMapOfFac` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFac`: the maps `I₁/I₁² ⟶ I₂/I₂²` and
  `B ⊗[A₁] Ω[A₁/R] ⟶ B ⊗[A₂] Ω[A₂/R]` induced by a factorisation `ψ ≫ φ₂ = φ₁` of one
  presentation of `B` through another.

## Main results

* `Stacks.Sites.Conormal.conormalSequence_exact` and
  `Stacks.Sites.Conormal.conormalSequence_epi`: the sequence of sheaves is exact at its middle
  term and its right-hand map is an epimorphism.
* `Stacks.Sites.Conormal.conormalSequence_f_class` and
  `Stacks.Sites.Conormal.conormalSequence_f_unique`: the left-hand map sends the conormal class
  of `f` to `1 ⊗ d f`, and that formula determines it.
* `Stacks.Sites.Conormal.conormalSequence_g_differential`: the right-hand map sends `1 ⊗ d f`
  to the differential of the image of `f`.
* `Stacks.Sites.Conormal.conormalSequence_f_naturality`: the left-hand maps of the conormal
  sequences of two presentations commute with the maps induced by a factorisation.
* `Stacks.Sites.Conormal.exists_covering_forall_exists_lift`: finitely many sections of `B` lift
  along a locally surjective `φ : A ⟶ B` on one common covering.
* `Stacks.Sites.Conormal.conormalSheafMapOfFac_id` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFac_id`: the identity factorisation induces the
  identity on both terms.

## Implementation notes

The ring universe and the two site universes are independent, and module values are lifted to a
universe large enough for sheafification on the site by `Stacks.Sites.Conormal.liftModules`.

The source writes the middle term's local sections as `d f ⊗ 1`; the tensor convention used
here writes them as `1 ⊗ d f`.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct


universe v u w z w'
namespace Stacks.Sites.Conormal
variable {C : Type u} [Category.{v} C]
variable {A B : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : A ⟶ B)

section CompositionOfPresentations

variable {A₁ A₂ A₃ : Cᵒᵖ ⥤ CommRingCat.{w}}
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (φ₃ : A₃ ⟶ B) (ψ : A₁ ⟶ A₂) (χ : A₂ ⟶ A₃)

/-- Applying a composite of morphisms of presheaves of commutative rings to a section applies
the two factors in turn. -/
lemma comp_app_apply (X : Cᵒᵖ) (x : A₁.obj X) :
    (ψ ≫ χ).app X x = χ.app X (ψ.app X x) := rfl

/-- The maps on the image presheaves induced by two composable factorisations compose. -/
lemma quotientMapOfFac_comp (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₃ = φ₂)
    (hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁) (X : Cᵒᵖ) (b : (quotientPresheaf φ₁).obj X) :
    quotientMapOfFac φ₁ φ₃ (ψ ≫ χ) hψχ X b =
      quotientMapOfFac φ₂ φ₃ χ hχ X (quotientMapOfFac φ₁ φ₂ ψ hψ X b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- The maps on conormal modules induced by two composable factorisations compose. -/
lemma conormalMapOfFac_comp (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₃ = φ₂)
    (hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁) (X : Cᵒᵖ) (c : (kernelIdeal φ₁ X).Cotangent) :
    conormalMapOfFac φ₁ φ₃ (ψ ≫ χ) hψχ X c =
      conormalMapOfFac φ₂ φ₃ χ hχ X (conormalMapOfFac φ₁ φ₂ ψ hψ X c) := by
  obtain ⟨x, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  change (kernelIdeal φ₃ X).toCotangent ⟨(ψ ≫ χ).app X (x : A₁.obj X), _⟩ =
    (kernelIdeal φ₃ X).toCotangent ⟨χ.app X (ψ.app X (x : A₁.obj X)), _⟩
  exact congrArg (kernelIdeal φ₃ X).toCotangent
    (Subtype.ext (comp_app_apply ψ χ X (x : A₁.obj X)))

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (a₃ : R ⟶ A₃)

/-- The map on tensor products induced by a factorisation sends `b ⊗ d x` to `b' ⊗ d (ψ x)`. -/
private lemma tensorMapOfFacₛₗ_tmul_d (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂) (X : Cᵒᵖ)
    (b : A₁.obj X ⧸ kernelIdeal φ₁ X) (x : A₁.obj X) :
    tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X
        (b ⊗ₜ[A₁.obj X] CommRingCat.KaehlerDifferential.d (f := a₁.app X) x) =
      quotientMapOfFac φ₁ φ₂ ψ hψ X b ⊗ₜ[A₂.obj X]
        CommRingCat.KaehlerDifferential.d (f := a₂.app X) (ψ.app X x) :=
  (TensorProduct.map_tmul _ _ _ _).trans (congrArg _ (differentialsMapOfFac_d ψ a₁ a₂ ha X x))

/-- The maps on relative differentials induced by two composable factorisations compose. -/
lemma differentialsMapOfFac_comp (ha : a₁ ≫ ψ = a₂) (hb : a₂ ≫ χ = a₃)
    (hab : a₁ ≫ (ψ ≫ χ) = a₃) (X : Cᵒᵖ) (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfFac (ψ ≫ χ) a₁ a₃ hab X ω =
      differentialsMapOfFac χ a₂ a₃ hb X (differentialsMapOfFac ψ a₁ a₂ ha X ω) := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      change differentialsMapOfFac (ψ ≫ χ) a₁ a₃ hab X
          (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x) =
        differentialsMapOfFac χ a₂ a₃ hb X (differentialsMapOfFac ψ a₁ a₂ ha X
          (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x))
      rw [differentialsMapOfFac_d, differentialsMapOfFac_d, differentialsMapOfFac_d,
        comp_app_apply]
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih => rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, ih, comp_app_apply]

/-- The maps on the objectwise tensor products induced by two composable factorisations
compose. -/
lemma tensorMapOfFacₛₗ_comp (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₃ = φ₂)
    (hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁) (ha : a₁ ≫ ψ = a₂) (hb : a₂ ≫ χ = a₃)
    (hab : a₁ ≫ (ψ ≫ χ) = a₃) (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfFacₛₗ φ₁ φ₃ (ψ ≫ χ) hψχ a₁ a₃ hab X t =
      tensorMapOfFacₛₗ φ₂ φ₃ χ hχ a₂ a₃ hb X (tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b ω =>
      refine (TensorProduct.map_tmul _ _ b ω).trans ?_
      refine Eq.symm (Eq.trans (congrArg (tensorMapOfFacₛₗ φ₂ φ₃ χ hχ a₂ a₃ hb X)
        (TensorProduct.map_tmul _ _ b ω)) ?_)
      refine (TensorProduct.map_tmul _ _ _ _).trans ?_
      exact congrArg₂ (fun b (ω : (differentialsPresheaf a₃).obj X) ↦ b ⊗ₜ[A₃.obj X] ω)
        (quotientMapOfFac_comp φ₁ φ₂ φ₃ ψ χ hψ hχ hψχ X b).symm
        (differentialsMapOfFac_comp ψ χ a₁ a₂ a₃ ha hb hab X ω).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end CompositionOfPresentations

section Lift
variable (S : Cᵒᵖ ⥤ RingCat.{w})
/-- Lift module values to a universe large enough for sheafification on the site.
The ring universe and both site universes remain independent. -/
noncomputable def liftModules : PresheafOfModules.{w} S ⥤ PresheafOfModules.{max w u v z} S where
  obj M :=
    { obj X := ModuleCat.of (S.obj X) (ULift.{max u v z} (M.obj X))
      map {X Y} f := (ModuleCat.uliftFunctor.{max u v z} (S.obj X)).map (M.map f)
      map_id X := by
        ext x
        change ULift.up (M.map (𝟙 X) x.down) = x
        rw [M.map_id]; rfl
      map_comp f g := by
        ext x
        change ULift.up (M.map (f ≫ g) x.down) = ULift.up (M.map g (M.map f x.down))
        rw [M.map_comp_apply]
        rfl }
  map f :=
    { app X := (ModuleCat.uliftFunctor.{max u v z} (S.obj X)).map (f.app X)
      naturality g := by
        ext x
        exact congrArg ULift.up (PresheafOfModules.naturality_apply f g x.down) }

/-- The objectwise universe lift of presheaves of modules is an additive functor. -/
instance : (liftModules.{v, u, w, z} S).Additive where
  map_add {X Y} f g := by ext U x; rfl

/-- The objectwise universe lift preserves exactness. -/
lemma liftModules_exact (K : ShortComplex (PresheafOfModules.{w} S))
    (h : ∀ X, Function.Exact (K.f.app X) (K.g.app X)) :
    (K.map (liftModules.{v, u, w, z} S)).Exact := by
  refine presheafComplex_exact _ fun X x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (h X x.down).mp (congrArg ULift.down hx)
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  · rintro ⟨y, rfl⟩
    exact congrArg ULift.up ((h X _).mpr ⟨y.down, rfl⟩)

end Lift


section Sheaves

variable (J : GrothendieckTopology C)

/-- Sheafification of presheaves of abelian groups exists on an essentially small site. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially small site, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification if and only if it is locally bijective. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)


/-- The locally bijective ring map from the image presheaf to the target sheaf. -/
noncomputable def quotientToRingSheaf :
    quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj :=
  Functor.whiskerRight (quotientToTarget φ.hom) (forget₂ CommRingCat RingCat)

/-- The map `quotientToRingSheaf J A B φ` is locally injective. -/
instance : Presheaf.IsLocallyInjective J (quotientToRingSheaf J A B φ) :=
  Presheaf.isLocallyInjective_of_injective _ _ (quotientToTarget_injective φ.hom)

/-- If `φ` is locally surjective, then so is `quotientToRingSheaf J A B φ`. -/
instance [Presheaf.IsLocallySurjective J φ.hom] :
    Presheaf.IsLocallySurjective J (quotientToRingSheaf J A B φ) where
  imageSieve_mem x := Presheaf.imageSieve_mem J (quotientToTarget φ.hom) x

/-- The conormal sheaf `I/I²`, with its canonical `B`-module structure. -/
noncomputable abbrev conormalSheaf [Presheaf.IsLocallySurjective J φ.hom] :
    _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  (PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
    ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom))

/-- The tensor product sheaf `B ⊗[A] Ω[A/R]`, in its image-presheaf model. -/
noncomputable abbrev tensorDifferentialsSheaf [Presheaf.IsLocallySurjective J φ.hom] :
    _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  (PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
    ((liftModules.{v, u, w, z} _).obj (tensorPresheaf φ.hom a.hom))

/-- The sheaf `Ω[B/R]`, as the associated sheaf of the relative differentials of the image
presheaf. -/
noncomputable abbrev imageDifferentialsSheaf [Presheaf.IsLocallySurjective J φ.hom] :
    _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  (PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
    ((liftModules.{v, u, w, z} _).obj (quotientDifferentialsPresheaf φ.hom a.hom))

/-- The canonical conormal sequence of sheaves of `B`-modules. Its terms are the associated
sheaves of `I/I²`, `(A/I) ⊗[A] Ω[A/R]` and `Ω[(A/I)/R]`; because `(A/I)` sheafifies to `B`,
these are the three terms `I/I²`, `B ⊗[A] Ω[A/R]` and `Ω[B/R]`. Tensor factors are written
with scalars first. -/
noncomputable def conormalSequence [Presheaf.IsLocallySurjective J φ.hom] :
    ShortComplex (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  ((conormalPresheafComplex φ.hom a.hom).map (liftModules.{v, u, w, z} _)).map
    (PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The conormal sequence of sheaves is exact at its middle term. -/
lemma conormalSequence_exact [Presheaf.IsLocallySurjective J φ.hom] :
    (conormalSequence.{v, u, w, z} J R A B a φ).Exact :=
  (liftModules_exact _ _ (conormalToTensor_exact φ.hom a.hom)).map _

/-- The right-hand map of the conormal sequence of sheaves is an epimorphism. -/
instance conormalSequence_epi [Presheaf.IsLocallySurjective J φ.hom] :
    Epi (conormalSequence.{v, u, w, z} J R A B a φ).g := by
  let L := liftModules.{v, u, w, z} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat)
  have : Epi (L.map (tensorToDifferentials φ.hom a.hom)) :=
    PresheafOfModules.epi_of_surjective fun X x ↦
      let ⟨y, hy⟩ := tensorToDifferentials_surjective φ.hom a.hom X x.down
      ⟨ULift.up y, congrArg ULift.up hy⟩
  change Epi ((PresheafOfModules.sheafification.{max w u v z}
    (quotientToRingSheaf J A B φ)).map (L.map (tensorToDifferentials φ.hom a.hom)))
  infer_instance

variable [Presheaf.IsLocallySurjective J φ.hom]

/-- The image of an objectwise section under the module sheafification unit. -/
noncomputable def toAssociatedModule
    (M : PresheafOfModules.{w} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat))
    (X : Cᵒᵖ) (x : M.obj X) :
    ((PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
      ((liftModules.{v, u, w, z} _).obj M)).val.obj X :=
  (((PresheafOfModules.sheafificationAdjunction.{max w u v z}
    (quotientToRingSheaf J A B φ)).unit.app
    ((liftModules.{v, u, w, z} _).obj M)).app X) (ULift.up x)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification preserves the formula for a map on presheaf sections. -/
lemma associatedModule_map_unit
    {M N : PresheafOfModules.{w} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat)}
    (f : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) :
    (((PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).map
        ((liftModules.{v, u, w, z} _).map f)).val.app X)
      (toAssociatedModule.{v, u, w, z} J A B φ M X x) =
        toAssociatedModule.{v, u, w, z} J A B φ N X (f.app X x) :=
  (congrArg (fun h ↦ (h.app X) (ULift.up x))
    ((PresheafOfModules.sheafificationAdjunction.{max w u v z}
      (quotientToRingSheaf J A B φ)).unit.naturality
      ((liftModules.{v, u, w, z} _).map f))).symm

/-! ### Morphisms out of a sheafified presheaf of modules -/

section Desc

variable (M : PresheafOfModules.{w} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sheafification unit is additive on sections. -/
lemma toAssociatedModule_add (X : Cᵒᵖ) (x y : M.obj X) :
    toAssociatedModule.{v, u, w, z} J A B φ M X (x + y) =
      toAssociatedModule.{v, u, w, z} J A B φ M X x +
        toAssociatedModule.{v, u, w, z} J A B φ M X y :=
  map_add (((PresheafOfModules.sheafificationAdjunction.{max w u v z}
    (quotientToRingSheaf J A B φ)).unit.app
      ((liftModules.{v, u, w, z} _).obj M)).app X).hom (ULift.up x) (ULift.up y)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sheafification unit is semilinear over the inclusion of the image presheaf. -/
lemma toAssociatedModule_smul (X : Cᵒᵖ) (r : (quotientPresheaf φ.hom).obj X) (x : M.obj X) :
    toAssociatedModule.{v, u, w, z} J A B φ M X (r • x) =
      (quotientToRingSheaf J A B φ).app X r •
        toAssociatedModule.{v, u, w, z} J A B φ M X x :=
  (((PresheafOfModules.sheafificationAdjunction.{max w u v z}
    (quotientToRingSheaf J A B φ)).unit.app
      ((liftModules.{v, u, w, z} _).obj M)).app X).hom.map_smul r (ULift.up x)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sheafification unit commutes with the restriction maps. -/
lemma toAssociatedModule_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    toAssociatedModule.{v, u, w, z} J A B φ M Y (M.map f x) =
      ((PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
        ((liftModules.{v, u, w, z} _).obj M)).val.map f
        (toAssociatedModule.{v, u, w, z} J A B φ M X x) :=
  PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{max w u v z}
      (quotientToRingSheaf J A B φ)).unit.app ((liftModules.{v, u, w, z} _).obj M))
    f (ULift.up x)

variable (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
  (u : ∀ X : Cᵒᵖ, M.obj X → N.val.obj X)

/-- A family of maps on sections which is additive, semilinear over the inclusion of the image
presheaf into `B`, and compatible with the restriction maps, as a morphism of presheaves of
modules into the restriction of scalars of `N`. -/
noncomputable def sheafifyLiftHom
    (hadd : ∀ (X : Cᵒᵖ) (x y : M.obj X), u X (x + y) = u X x + u X y)
    (hsmul : ∀ (X : Cᵒᵖ) (r : (quotientPresheaf φ.hom).obj X) (x : M.obj X),
      u X (r • x) = (quotientToRingSheaf J A B φ).app X r • u X x)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : M.obj X),
      u Y (M.map f x) = N.val.map f (u X x)) :
    (liftModules.{v, u, w, z} _).obj M ⟶
      (PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
        ((_root_.SheafOfModules.forget _).obj N) where
  app X := ModuleCat.ofHom
    (X := ((liftModules.{v, u, w, z} _).obj M).obj X)
    (Y := ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
      ((_root_.SheafOfModules.forget _).obj N)).obj X)
    { toFun := fun x ↦ u X x.down
      map_add' := fun x y ↦ hadd X x.down y.down
      map_smul' := fun r x ↦ hsmul X r x.down }
  naturality {X Y} f := ModuleCat.hom_ext (LinearMap.ext fun x ↦ hnat X Y f x.down)

/-- The morphism of sheaves of `B`-modules out of the sheafification of `M` determined by a
compatible family of maps on presheaf sections. -/
noncomputable def sheafifyLiftDesc
    (hadd : ∀ (X : Cᵒᵖ) (x y : M.obj X), u X (x + y) = u X x + u X y)
    (hsmul : ∀ (X : Cᵒᵖ) (r : (quotientPresheaf φ.hom).obj X) (x : M.obj X),
      u X (r • x) = (quotientToRingSheaf J A B φ).app X r • u X x)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : M.obj X),
      u Y (M.map f x) = N.val.map f (u X x)) :
    (PresheafOfModules.sheafification.{max w u v z} (quotientToRingSheaf J A B φ)).obj
        ((liftModules.{v, u, w, z} _).obj M) ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv.{max w u v z}
    (quotientToRingSheaf J A B φ)).symm
      (sheafifyLiftHom.{v, u, w, z} J A B φ M N u hadd hsmul hnat)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On presheaf sections the morphism classifying `u` is `u`. -/
lemma sheafifyLiftDesc_toAssociatedModule
    (hadd : ∀ (X : Cᵒᵖ) (x y : M.obj X), u X (x + y) = u X x + u X y)
    (hsmul : ∀ (X : Cᵒᵖ) (r : (quotientPresheaf φ.hom).obj X) (x : M.obj X),
      u X (r • x) = (quotientToRingSheaf J A B φ).app X r • u X x)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : M.obj X),
      u Y (M.map f x) = N.val.map f (u X x))
    (X : Cᵒᵖ) (x : M.obj X) :
    ((sheafifyLiftDesc.{v, u, w, z} J A B φ M N u hadd hsmul hnat).val.app X)
      (toAssociatedModule.{v, u, w, z} J A B φ M X x) = u X x :=
  congrArg (fun t : (liftModules.{v, u, w, z} _).obj M ⟶
      (PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
        ((_root_.SheafOfModules.forget _).obj N) ↦ (t.app X) (ULift.up x))
    ((PresheafOfModules.sheafificationHomEquiv.{max w u v z}
      (quotientToRingSheaf J A B φ)).apply_symm_apply
        (sheafifyLiftHom.{v, u, w, z} J A B φ M N u hadd hsmul hnat))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two morphisms out of the sheafification of `M` agreeing on presheaf sections are equal. -/
lemma sheafify_hom_ext
    {g₁ g₂ : (PresheafOfModules.sheafification.{max w u v z}
        (quotientToRingSheaf J A B φ)).obj ((liftModules.{v, u, w, z} _).obj M) ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X),
      g₁.val.app X (toAssociatedModule.{v, u, w, z} J A B φ M X x) =
        g₂.val.app X (toAssociatedModule.{v, u, w, z} J A B φ M X x)) :
    g₁ = g₂ := by
  apply (PresheafOfModules.sheafificationHomEquiv.{max w u v z}
    (quotientToRingSheaf J A B φ)).injective
  ext X ⟨x⟩
  exact h X x

end Desc

/-- The section of the conormal sheaf represented by a section of the kernel ideal. -/
noncomputable def conormalClass (X : Cᵒᵖ) (x : kernelIdeal φ.hom X) :
    (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.obj X :=
  toAssociatedModule J A B φ (conormalPresheaf φ.hom) X ((kernelIdeal φ.hom X).toCotangent x)

/-- The local section `1 ⊗ d f` of the middle sheaf. -/
noncomputable def tensorDifferential (X : Cᵒᵖ) (x : A.obj.obj X) :
    (conormalSequence.{v, u, w, z} J R A B a φ).X₂.val.obj X :=
  toAssociatedModule J A B φ (tensorPresheaf φ.hom a.hom) X
    ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
      CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x)

/-- The differential of a section of the image presheaf, viewed in `Ω[B/R]`. -/
noncomputable def quotientDifferential (X : Cᵒᵖ)
    (x : A.obj.obj X ⧸ kernelIdeal φ.hom X) :
    (conormalSequence.{v, u, w, z} J R A B a φ).X₃.val.obj X :=
  toAssociatedModule J A B φ (quotientDifferentialsPresheaf φ.hom a.hom) X
    (CommRingCat.KaehlerDifferential.d (f := (a.hom ≫ toQuotient φ.hom).app X) x)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The right-hand map sends `1 ⊗ d f` to the differential of the image of `f`. -/
lemma conormalSequence_g_differential (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((conormalSequence.{v, u, w, z} J R A B a φ).g.val.app X)
      (tensorDifferential.{v, u, w, z} J R A B a φ X x) =
        quotientDifferential.{v, u, w, z} J R A B a φ X (Ideal.Quotient.mk _ x) := by
  refine (associatedModule_map_unit J A B φ (tensorToDifferentials φ.hom a.hom) X
    ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
      CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x)).trans ?_
  exact congrArg (toAssociatedModule J A B φ (quotientDifferentialsPresheaf φ.hom a.hom) X)
    ((tensorToDifferentialsApp_tmul_d φ.hom a.hom X 1 x).trans (one_smul _ _))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The left-hand map sends the conormal class of `f` to `1 ⊗ d f`, which is the source
convention `d f ⊗ 1` with tensor factors interchanged. -/
lemma conormalSequence_f_class (X : Cᵒᵖ) (x : kernelIdeal φ.hom X) :
    ((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app X)
      (conormalClass.{v, u, w, z} J R A B a φ X x) =
        tensorDifferential.{v, u, w, z} J R A B a φ X x :=
  (associatedModule_map_unit J A B φ (conormalToTensor φ.hom a.hom) X
    ((kernelIdeal φ.hom X).toCotangent x)).trans
      (congrArg (toAssociatedModule J A B φ (tensorPresheaf φ.hom a.hom) X)
        (conormalToTensorApp_toCotangent φ.hom a.hom X x))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The formula on local conormal classes uniquely determines the left-hand map. -/
lemma conormalSequence_f_unique
    (g : (conormalSequence.{v, u, w, z} J R A B a φ).X₁ ⟶
      (conormalSequence.{v, u, w, z} J R A B a φ).X₂)
    (hg : ∀ (X : Cᵒᵖ) (x : kernelIdeal φ.hom X),
      g.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x) =
        tensorDifferential.{v, u, w, z} J R A B a φ X x) :
    g = (conormalSequence.{v, u, w, z} J R A B a φ).f := by
  apply (PresheafOfModules.sheafificationHomEquiv.{max w u v z}
    (quotientToRingSheaf J A B φ)).injective
  ext X ⟨x⟩
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective x
  exact (hg X x).trans (conormalSequence_f_class J R A B a φ X x).symm

/-! ### Functoriality of the conormal sequence in the presentation -/

/-- The underlying morphisms of presheaves of a factorisation of morphisms of sheaves of
commutative rings. -/
lemma hom_of_comp_eq {K : GrothendieckTopology C} {S₁ S₂ S₃ : Sheaf K CommRingCat.{w}}
    {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} {h : S₁ ⟶ S₃} (e : f ≫ g = h) :
    f.hom ≫ g.hom = h.hom :=
  congrArg (fun t : S₁ ⟶ S₃ ↦ t.hom) e

section ChangeOfPresentation

variable (A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hψ in
/-- The map of conormal sheaves `I₁/I₁² ⟶ I₂/I₂²` induced by a factorisation
`ψ ≫ φ₂ = φ₁`. -/
noncomputable def conormalSheafMapOfFac :
    conormalSheaf.{v, u, w, z} J A₁ B φ₁ ⟶ conormalSheaf.{v, u, w, z} J A₂ B φ₂ := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom)
    (conormalSheaf.{v, u, w, z} J A₂ B φ₂)
    (fun X c ↦ toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
      (conormalMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X c)) ?_ ?_ ?_
  · intro X c c'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (map_add (conormalMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X) c c')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X _ _)
  · intro X r c
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (map_smulₛₗ (conormalMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X) r c)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B φ₂
      (conormalPresheaf φ₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (conormalMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X c))
      (quotientToTarget_quotientMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X r)
  · intro X Y f c
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) Y)
      (conormalMapOfFac_naturality φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) f c)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) f _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ in
/-- The induced map sends the conormal class of `f` to the conormal class of `ψ f`. -/
lemma conormalSheafMapOfFac_conormalClass (X : Cᵒᵖ) (x : kernelIdeal φ₁.hom X) :
    ((conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app X)
      (conormalClass.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
      conormalClass.{v, u, w, z} J R A₂ B a₂ φ₂ X
        ⟨ψ.hom.app X x, kernelIdeal_le_comap φ₁.hom φ₂.hom ψ.hom
          (hom_of_comp_eq hψ) X x.2⟩ := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

include hψ ha in
/-- The map `B ⊗[A₁] Ω[A₁/R] ⟶ B ⊗[A₂] Ω[A₂/R]` induced by a factorisation
`ψ ≫ φ₂ = φ₁` over `R`. -/
noncomputable def tensorSheafMapOfFac :
    tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ⟶
      tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂ := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom)
    (tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂)
    (fun X t ↦ toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
      (tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
        (hom_of_comp_eq ha) X t)) ?_ ?_ ?_
  · intro X t t'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂
        (tensorPresheaf φ₂.hom a₂.hom) X)
      (map_add (tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
        (hom_of_comp_eq ha) X) t t')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X _ _)
  · intro X r t
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂
        (tensorPresheaf φ₂.hom a₂.hom) X)
      (tensorMapOfFacₛₗ_smul φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
        (hom_of_comp_eq ha) X r t)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B φ₂
      (tensorPresheaf φ₂.hom a₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
          (hom_of_comp_eq ha) X t))
      (quotientToTarget_quotientMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X r)
  · intro X Y f t
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂
        (tensorPresheaf φ₂.hom a₂.hom) Y)
      (tensorMapOfFacₛₗ_naturality φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
        (hom_of_comp_eq ha) f t)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) f _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ ha in
/-- The induced map sends `1 ⊗ d f` to `1 ⊗ d (ψ f)`. -/
lemma tensorSheafMapOfFac_tensorDifferential (X : Cᵒᵖ) (x : A₁.obj.obj X) :
    ((tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val.app X)
      (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
      tensorDifferential.{v, u, w, z} J R A₂ B a₂ φ₂ X (ψ.hom.app X x) := by
  have h : ((tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val.app X)
      (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
          (hom_of_comp_eq ha) X
          ((1 : A₁.obj.obj X ⧸ kernelIdeal φ₁.hom X) ⊗ₜ[A₁.obj.obj X]
            CommRingCat.KaehlerDifferential.d (f := a₁.hom.app X) x)) := by
    apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}
  refine h.trans ?_
  refine congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂
    (tensorPresheaf φ₂.hom a₂.hom) X) ?_
  rw [tensorMapOfFacₛₗ_tmul_d, map_one]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ ha in
/-- The left-hand maps of the two conormal sequences commute with the maps induced by a
factorisation. -/
lemma conormalSequence_f_naturality :
    (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
        tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha =
      conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ ≫
        (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom X).toCotangent_surjective c
  refine Eq.trans (congrArg
    ((tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val.app X)
    (conormalSequence_f_class.{v, u, w, z} J R A₁ B a₁ φ₁ X c)) ?_
  refine Eq.trans (tensorSheafMapOfFac_tensorDifferential.{v, u, w, z}
    J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha X c) ?_
  refine Eq.symm (Eq.trans (congrArg
    ((conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f.val.app X)
    (conormalSheafMapOfFac_conormalClass.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ X c)) ?_)
  exact conormalSequence_f_class.{v, u, w, z} J R A₂ B a₂ φ₂ X _

end ChangeOfPresentation

section CompositionChangeOfPresentation

variable (A₁ A₂ A₃ : Sheaf J CommRingCat.{w})
  (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (a₃ : R ⟶ A₃)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (φ₃ : A₃ ⟶ B) (ψ : A₁ ⟶ A₂) (χ : A₂ ⟶ A₃)
  (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₃ = φ₂) (ha : a₁ ≫ ψ = a₂) (hb : a₂ ≫ χ = a₃)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [Presheaf.IsLocallySurjective J φ₃.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ in
/-- On presheaf sections, the map of conormal sheaves induced by a factorisation is the
objectwise map of conormal modules. -/
lemma conormalSheafMapOfFac_toAssociatedModule (X : Cᵒᵖ)
    (c : (conormalPresheaf φ₁.hom).obj X) :
    ((conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app X)
      (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom) X c) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (conormalMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X c) := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ ha in
/-- On presheaf sections, the map of tensor-differentials sheaves induced by a factorisation is
the objectwise map of tensor products. -/
lemma tensorSheafMapOfFac_toAssociatedModule (X : Cᵒᵖ)
    (t : (tensorPresheaf φ₁.hom a₁.hom).obj X) :
    ((tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val.app X)
      (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom) X t) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) a₁.hom a₂.hom
          (hom_of_comp_eq ha) X t) := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ hχ in
/-- The maps of conormal sheaves compose. -/
lemma conormalSheafMapOfFac_comp :
    conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ ≫
        conormalSheafMapOfFac.{v, u, w, z} J B A₂ A₃ φ₂ φ₃ χ hχ =
      conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₃ φ₁ φ₃ (ψ ≫ χ)
        (by rw [Category.assoc, hχ, hψ]) := by
  have hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁ := by rw [Category.assoc, hχ, hψ]
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  refine Eq.trans (congrArg
    ((conormalSheafMapOfFac.{v, u, w, z} J B A₂ A₃ φ₂ φ₃ χ hχ).val.app X)
    (conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ X c)) ?_
  refine (conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z}
    J B A₂ A₃ φ₂ φ₃ χ hχ X _).trans ?_
  refine Eq.symm (Eq.trans
    (conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z} J B A₁ A₃ φ₁ φ₃ (ψ ≫ χ) hψχ X c) ?_)
  exact congrArg (toAssociatedModule.{v, u, w, z} J A₃ B φ₃ (conormalPresheaf φ₃.hom) X)
    (conormalMapOfFac_comp φ₁.hom φ₂.hom φ₃.hom ψ.hom χ.hom (hom_of_comp_eq hψ)
      (hom_of_comp_eq hχ) (hom_of_comp_eq hψχ) X c)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hψ hχ ha hb in
/-- The maps of tensor-differentials sheaves compose. -/
lemma tensorSheafMapOfFac_comp :
    tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        tensorSheafMapOfFac.{v, u, w, z} J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb =
      tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₃ a₁ a₃ φ₁ φ₃ (ψ ≫ χ)
        (by rw [Category.assoc, hχ, hψ]) (by rw [← Category.assoc, ha, hb]) := by
  have hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁ := by rw [Category.assoc, hχ, hψ]
  have hab : a₁ ≫ (ψ ≫ χ) = a₃ := by rw [← Category.assoc, ha, hb]
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  refine Eq.trans (congrArg
    ((tensorSheafMapOfFac.{v, u, w, z} J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb).val.app X)
    (tensorSheafMapOfFac_toAssociatedModule.{v, u, w, z}
      J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha X t)) ?_
  refine (tensorSheafMapOfFac_toAssociatedModule.{v, u, w, z}
    J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb X _).trans ?_
  refine Eq.symm (Eq.trans (tensorSheafMapOfFac_toAssociatedModule.{v, u, w, z}
    J R B A₁ A₃ a₁ a₃ φ₁ φ₃ (ψ ≫ χ) hψχ hab X t) ?_)
  exact congrArg (toAssociatedModule.{v, u, w, z} J A₃ B φ₃
      (tensorPresheaf φ₃.hom a₃.hom) X)
    (tensorMapOfFacₛₗ_comp φ₁.hom φ₂.hom φ₃.hom ψ.hom χ.hom a₁.hom a₂.hom a₃.hom
      (hom_of_comp_eq hψ) (hom_of_comp_eq hχ) (hom_of_comp_eq hψχ) (hom_of_comp_eq ha)
      (hom_of_comp_eq hb) (hom_of_comp_eq hab) X t)

end CompositionChangeOfPresentation

section IdentityChangeOfPresentation

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The map of conormal sheaves induced by the identity factorisation is the identity. -/
lemma conormalSheafMapOfFac_id :
    conormalSheafMapOfFac.{v, u, w, z} J B A A φ φ (𝟙 A) (Category.id_comp φ) = 𝟙 _ := by
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (conormalPresheaf φ.hom)
  intro X c
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective c
  exact conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z} J B A A φ φ (𝟙 A)
    (Category.id_comp φ) X _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The map of tensor-differentials sheaves induced by the identity factorisation is the
identity. -/
lemma tensorSheafMapOfFac_id :
    tensorSheafMapOfFac.{v, u, w, z} J R B A A a a φ φ (𝟙 A) (Category.id_comp φ)
      (Category.comp_id a) = 𝟙 _ := by
  have hψ : (𝟙 A : A ⟶ A).hom ≫ φ.hom = φ.hom := hom_of_comp_eq (Category.id_comp φ)
  have ha : a.hom ≫ (𝟙 A : A ⟶ A).hom = a.hom := hom_of_comp_eq (Category.comp_id a)
  have hquot : ∀ (X : Cᵒᵖ) (b : A.obj.obj X ⧸ kernelIdeal φ.hom X),
      quotientMapOfFac φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ X b = b := by
    intro X b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rfl
  have hsmul : ∀ (X : Cᵒᵖ) (r : (quotientPresheaf φ.hom).obj X)
      (t : (A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗[A.obj.obj X]
        ((differentialsPresheaf a.hom).obj X)),
      tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X (r • t) =
        r • tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X t := by
    intro X r t
    refine (tensorMapOfFacₛₗ_smul φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ
      a.hom a.hom ha X r t).trans ?_
    exact congrArg (fun s : A.obj.obj X ⧸ kernelIdeal φ.hom X ↦
      s • tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X t) (hquot X r)
  have htensor : ∀ (X : Cᵒᵖ) (t : (A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗[A.obj.obj X]
        ((differentialsPresheaf a.hom).obj X)),
      tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X t = t := by
    intro X
    let F := tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X
    have key : (LinearMap.mk (AddHom.mk (fun t ↦ F t) (map_add F)) (hsmul X) :
        tensorObj φ.hom a.hom X →ₗ[(quotientPresheaf φ.hom).obj X]
          tensorObj φ.hom a.hom X) = LinearMap.id := by
      apply tensor_hom_ext φ.hom a.hom X
      intro b x
      change tensorMapOfFacₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom hψ a.hom a.hom ha X
            (b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x) =
          b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x
      rw [tensorMapOfFacₛₗ_tmul_d, hquot]
      rfl
    exact fun t ↦ LinearMap.congr_fun key t
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom)
  intro X t
  exact (tensorSheafMapOfFac_toAssociatedModule.{v, u, w, z} J R B A A a a φ φ (𝟙 A)
    (Category.id_comp φ) (Category.comp_id a) X t).trans (congrArg
    (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X) (htensor X t))

end IdentityChangeOfPresentation

end Sheaves

/-! ### Lifting finitely many sections along a locally surjective presentation -/

section FiniteLifting

variable (J : GrothendieckTopology C)

/-- A finite family of sections of `B` over `X` lifts along a locally surjective morphism
`φ : A ⟶ B` of presheaves of commutative rings on one common covering of `X`: the intersection
of the image sieves of the members of the family is again a covering sieve, and over every
arrow of it every member of the family is a value of `φ`. -/
theorem exists_covering_forall_exists_lift [Presheaf.IsLocallySurjective J φ] {X : C}
    (s : Finset (B.obj (op X))) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g → ∀ b ∈ s,
      ∃ t : A.obj (op Y), φ.app (op Y) t = B.map g.op b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, J.top_mem X, by simp⟩
  | @insert b t _ ih =>
      obtain ⟨S, hS, hlift⟩ := ih
      refine ⟨S ⊓ Presheaf.imageSieve φ b, J.intersection_covering hS
        (Presheaf.imageSieve_mem J φ b), fun Y g hg c hc ↦ ?_⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hg.2
      · exact hlift Y g hg.1 c hc

end FiniteLifting

end Stacks.Sites.Conormal
