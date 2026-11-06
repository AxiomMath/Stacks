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

/-!
# The objectwise conormal sequence of a quotient of presheaves of rings

Let `R ⟶ A ⟶ B` be morphisms of presheaves of commutative rings on a category `C`. Writing `I`
for the kernel of `A ⟶ B`, this file constructs the objectwise conormal sequence

`I/I² ⟶ (A/I) ⊗[A] Ω[A/R] ⟶ Ω[(A/I)/R] ⟶ 0`

as a short complex of presheaves of modules over the *image presheaf* `Q(U) = A(U)/I(U)`, and
proves that it is exact with surjective right-hand map. The conormal presheaf has sections
`I(U)/I(U)²`, the middle presheaf has sections `(A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]`, and the
right-hand presheaf is the presheaf of relative differentials of `Q` over `R`. It then constructs
the maps between the terms of two such sequences induced by a change of presentation: along a
commutative square, and along a factorisation `ψ ≫ φ₂ = φ₁` of one presentation of `B` through
another.

The sheafified conormal sequence is built from these in
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence.Sheaf`.

## Main definitions

* `Stacks.Sites.Conormal.quotientPresheaf`: the image presheaf `U ↦ A(U)/I(U)`.
* `Stacks.Sites.Conormal.conormalPresheaf`: the presheaf `U ↦ I(U)/I(U)²`.
* `Stacks.Sites.Conormal.tensorPresheaf`: the presheaf `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]`.
* `Stacks.Sites.Conormal.conormalPresheafComplex`: the objectwise conormal sequence, as a short
  complex of presheaves of modules over the image presheaf.
* `Stacks.Sites.Conormal.quotientMapOfSquare`, `Stacks.Sites.Conormal.conormalMapOfSquare`,
  `Stacks.Sites.Conormal.differentialsMapOfSquare` and
  `Stacks.Sites.Conormal.tensorMapOfSquareₛₗ`: the maps between the terms induced by a
  commutative square of presentations.
* `Stacks.Sites.Conormal.quotientMapOfFac`, `Stacks.Sites.Conormal.conormalMapOfFac`,
  `Stacks.Sites.Conormal.differentialsMapOfFac` and `Stacks.Sites.Conormal.tensorMapOfFacₛₗ`:
  the maps induced by a factorisation of one presentation through another.

## Main results

* `Stacks.Sites.Conormal.conormalPresheafComplex_exact`: the objectwise sequence is exact.

## Implementation notes

Several constructions are stated twice: once as a semilinear map between the underlying modules
and once as a morphism of module objects. The semilinear form is where the module structures are
the canonical ones, so equations proved there transfer to the bundled form by a defeq check
rather than by rewriting across the bundling.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), whose
  commutative-algebra core is `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct


universe v u w z w'
namespace Stacks.Sites.Conormal
variable {C : Type u} [Category.{v} C]
variable {A B : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : A ⟶ B)

/-- The presheaf kernel ideal, evaluated at an object of the site. -/
abbrev kernelIdeal (X : Cᵒᵖ) : Ideal (A.obj X) := RingHom.ker (φ.app X).hom

/-- Restriction maps preserve the kernel ideal. -/
lemma map_kernel {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    kernelIdeal φ X ≤ (kernelIdeal φ Y).comap (A.map f).hom := by
  intro x hx
  change φ.app Y (A.map f x) = 0
  rw [φ.naturality_apply, (show φ.app X x = 0 from hx), map_zero]

/-- The objectwise quotient by the kernel. This is canonically the image presheaf,
which need not be a sheaf. -/
noncomputable abbrev quotientPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj X := CommRingCat.of (A.obj X ⧸ kernelIdeal φ X)
  map f := CommRingCat.ofHom (Ideal.quotientMap _ (A.map f).hom (map_kernel φ f))
  map_id X := by
    ext x
    change Ideal.Quotient.mk _ (A.map (𝟙 X) x) = Ideal.Quotient.mk _ x
    rw [A.map_id]; rfl
  map_comp f g := by
    ext x
    change Ideal.Quotient.mk _ (A.map (f ≫ g) x) =
      Ideal.Quotient.mk _ (A.map g (A.map f x))
    rw [A.map_comp]; rfl

/-- The objectwise surjection onto the image presheaf. -/
noncomputable def toQuotient : A ⟶ quotientPresheaf φ where
  app X := CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- The canonical inclusion of the image presheaf into the target. -/
noncomputable def quotientToTarget : quotientPresheaf φ ⟶ B where
  app X := CommRingCat.ofHom (Ideal.Quotient.lift _ (φ.app X).hom (fun _ hx ↦ hx))
  naturality {X Y} f := by
    ext x
    exact φ.naturality_apply f x

/-- The image presheaf embeds into the target on every object. -/
lemma quotientToTarget_injective (X : Cᵒᵖ) :
    Function.Injective ((quotientToTarget φ).app X) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Ideal.Quotient.eq.mpr <| (map_sub (φ.app X).hom x y).trans (sub_eq_zero.mpr h)

/-- The map `quotientToTarget φ` is locally injective for every Grothendieck topology. -/
instance (J : GrothendieckTopology C) :
    Presheaf.IsLocallyInjective J (quotientToTarget φ) :=
  Presheaf.isLocallyInjective_of_injective _ _ (quotientToTarget_injective φ)

/-- If `φ` is locally surjective, then so is `quotientToTarget φ`. -/
instance (J : GrothendieckTopology C) [Presheaf.IsLocallySurjective J φ] :
    Presheaf.IsLocallySurjective J (quotientToTarget φ) where
  imageSieve_mem {X} x := by
    apply J.superset_covering _ (Presheaf.imageSieve_mem J φ x)
    rintro Y f ⟨a, ha⟩
    exact ⟨Ideal.Quotient.mk _ a, ha⟩

section Cotangent
variable {S : Type w} {T : Type w'} [CommRing S] [CommRing T]
  (I : Ideal S) (K : Ideal T) (f : S →+* T) (hf : I ≤ K.comap f)

/-- If `I ≤ f⁻¹(K)`, then also `I ≤ f⁻¹(K)` for `f` viewed as a `ℤ`-algebra map. -/
lemma le_comap_toIntAlgHom (h : I ≤ K.comap f) :
    I ≤ K.comap (f.toIntAlgHom : S →ₐ[ℤ] T) := h

/-- The semilinear map `I/I² → K/K²` on conormal modules induced by a ring map `f` with
`I ≤ f⁻¹(K)`, semilinear over the induced map `S/I → T/K`. -/
noncomputable def cotangentMap : I.Cotangent →ₛₗ[Ideal.quotientMap K f hf] K.Cotangent where
  toFun := Ideal.mapCotangent I K f.toIntAlgHom (le_comap_toIntAlgHom I K f hf)
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    change K.toCotangent ⟨f (r * x), _⟩ = K.toCotangent (f r • ⟨f x, _⟩)
    congr 1
    ext
    exact map_mul f r x

/-- The restriction of a conormal class is the class of the restriction. -/
@[simp]
lemma cotangentMap_toCotangent (x : I) :
    cotangentMap I K f hf (I.toCotangent x) = K.toCotangent ⟨f x, hf x.2⟩ := rfl
end Cotangent

/-- The presheaf `U ↦ I(U)/I(U)²`, with its natural `A/I`-module structure. -/
noncomputable def conormalPresheaf :
    PresheafOfModules.{w} (quotientPresheaf φ ⋙ forget₂ _ RingCat) where
  obj X := ModuleCat.of (A.obj X ⧸ kernelIdeal φ X) (kernelIdeal φ X).Cotangent
  map {X Y} f := ModuleCat.ofHom
    (X := ModuleCat.of (A.obj X ⧸ kernelIdeal φ X) (kernelIdeal φ X).Cotangent)
    (Y := (ModuleCat.restrictScalars ((quotientPresheaf φ).map f).hom).obj
      (ModuleCat.of (A.obj Y ⧸ kernelIdeal φ Y) (kernelIdeal φ Y).Cotangent))
    { toFun := cotangentMap _ _ (A.map f).hom (map_kernel φ f)
      map_add' := map_add _
      map_smul' := (cotangentMap _ _ (A.map f).hom (map_kernel φ f)).map_smul' }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
    change (kernelIdeal φ X).toCotangent ⟨A.map (𝟙 X) x, _⟩ = (kernelIdeal φ X).toCotangent x
    congr 1
    ext
    simp
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
    change (kernelIdeal φ Z).toCotangent ⟨A.map (f ≫ g) x, _⟩ =
      (kernelIdeal φ Z).toCotangent ⟨A.map g (A.map f x), _⟩
    congr 1
    ext
    change A.map (f ≫ g) x = A.map g (A.map f x)
    rw [A.map_comp]; rfl

section Tensor
variable {R : Cᵒᵖ ⥤ CommRingCat.{w}} (a : R ⟶ A)

/-- The objectwise presheaf of relative Kähler differentials. -/
noncomputable abbrev differentialsPresheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' a

/-- The objectwise tensor product `(A/I) ⊗[A] Ω[A/R]`. -/
noncomputable def tensorObj (X : Cᵒᵖ) : ModuleCat.{w} ((quotientPresheaf φ).obj X) :=
  ModuleCat.of (A.obj X ⧸ kernelIdeal φ X)
    ((A.obj X ⧸ kernelIdeal φ X) ⊗[A.obj X] ((differentialsPresheaf a).obj X))

/-- Restriction on the image presheaf, as a semilinear map of quotient rings. -/
noncomputable def quotientRestrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (A.obj X ⧸ kernelIdeal φ X) →ₛₗ[(A.map f).hom] (A.obj Y ⧸ kernelIdeal φ Y) where
  toFun := (quotientPresheaf φ).map f
  map_add' := map_add ((quotientPresheaf φ).map f).hom
  map_smul' r x := by
    change Ideal.quotientMap _ (A.map f).hom (map_kernel φ f) (Ideal.Quotient.mk _ r * x) =
      Ideal.Quotient.mk _ (A.map f r) * Ideal.quotientMap _ (A.map f).hom (map_kernel φ f) x
    rw [map_mul]; rfl

/-- Restriction on the tensor product, before bundling as a map of module objects. -/
noncomputable def tensorMapₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((A.obj X ⧸ kernelIdeal φ X) ⊗[A.obj X] ((differentialsPresheaf a).obj X)) →ₛₗ[(A.map f).hom]
      ((A.obj Y ⧸ kernelIdeal φ Y) ⊗[A.obj Y] ((differentialsPresheaf a).obj Y)) :=
  TensorProduct.map (quotientRestrictₛₗ φ f) ((differentialsPresheaf a).restrictₛₗ f)

/-- Restriction on the tensor product is semilinear over the restriction on `A/I`. -/
lemma tensorMapₛₗ_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : A.obj X ⧸ kernelIdeal φ X)
    (x : (A.obj X ⧸ kernelIdeal φ X) ⊗[A.obj X] ((differentialsPresheaf a).obj X)) :
    tensorMapₛₗ φ a f (r • x) = ((quotientPresheaf φ).map f r) • tensorMapₛₗ φ a f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    change tensorMapₛₗ φ a f ((r * b) ⊗ₜ ω) =
      ((quotientPresheaf φ).map f r) • tensorMapₛₗ φ a f (b ⊗ₜ ω)
    simp only [tensorMapₛₗ, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    exact map_mul ((quotientPresheaf φ).map f).hom r b
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Restriction on the tensor product, semilinear over the restriction on `A/I`. -/
noncomputable def tensorMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    tensorObj φ a X ⟶ (ModuleCat.restrictScalars ((quotientPresheaf φ).map f).hom).obj
      (tensorObj φ a Y) :=
  ModuleCat.ofHom (X := tensorObj φ a X)
    (Y := (ModuleCat.restrictScalars ((quotientPresheaf φ).map f).hom).obj (tensorObj φ a Y))
    { toFun := tensorMapₛₗ φ a f
      map_add' := map_add (tensorMapₛₗ φ a f)
      map_smul' := tensorMapₛₗ_smul φ a f }

/-- Restriction along an identity acts trivially on the tensor product. -/
lemma tensorMapₛₗ_id (X : Cᵒᵖ)
    (x : (A.obj X ⧸ kernelIdeal φ X) ⊗[A.obj X] ((differentialsPresheaf a).obj X)) :
    tensorMapₛₗ φ a (𝟙 X) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul b ω =>
    refine (TensorProduct.map_tmul _ _ b ω).trans ?_
    exact congrArg₂ (fun b (ω : (differentialsPresheaf a).obj X) ↦ b ⊗ₜ[A.obj X] ω)
      (ConcreteCategory.congr_hom ((quotientPresheaf φ).map_id X) b)
      (ConcreteCategory.congr_hom ((differentialsPresheaf a).map_id X) ω)
  | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)

/-- Restriction on the tensor product is compatible with composition. -/
lemma tensorMapₛₗ_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (A.obj X ⧸ kernelIdeal φ X) ⊗[A.obj X] ((differentialsPresheaf a).obj X)) :
    tensorMapₛₗ φ a (f ≫ g) x = tensorMapₛₗ φ a g (tensorMapₛₗ φ a f x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul b ω =>
    refine (TensorProduct.map_tmul _ _ b ω).trans ?_
    refine Eq.trans ?_ (congrArg (tensorMapₛₗ φ a g) (TensorProduct.map_tmul _ _ b ω)).symm
    refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
    exact congrArg₂ (fun b (ω : (differentialsPresheaf a).obj Z) ↦ b ⊗ₜ[A.obj Z] ω)
      (ConcreteCategory.congr_hom ((quotientPresheaf φ).map_comp f g) b)
      ((differentialsPresheaf a).map_comp_apply f g ω)
  | add x y hx hy =>
    refine (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans ?_)
    exact (map_add (tensorMapₛₗ φ a g) _ _).symm.trans
      (congrArg (tensorMapₛₗ φ a g) (map_add (tensorMapₛₗ φ a f) x y).symm)

/-- The presheaf `(A/I) ⊗[A] Ω[A/R]` whose associated sheaf is the middle term. -/
noncomputable def tensorPresheaf :
    PresheafOfModules.{w} (quotientPresheaf φ ⋙ forget₂ _ RingCat) where
  obj := tensorObj φ a
  map := tensorMap φ a
  map_id X := ModuleCat.hom_ext (LinearMap.ext (tensorMapₛₗ_id φ a X))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext (tensorMapₛₗ_comp φ a f g))
/-- A tensor of a scalar and a differential, read as a section of the tensor presheaf.
The result type carries the identification with the module object, so that equations
between such sections can be composed instead of rewritten through it. -/
noncomputable abbrev tmulOver (X : Cᵒᵖ) (b : A.obj X ⧸ kernelIdeal φ X)
    (ω : (differentialsPresheaf a).obj X) : tensorObj φ a X :=
  b ⊗ₜ[A.obj X] ω

/-- Maps from the tensor product are determined by tensors of universal differentials. -/
lemma tensor_hom_ext (X : Cᵒᵖ) {M : ModuleCat.{z} ((quotientPresheaf φ).obj X)}
    (f g : tensorObj φ a X →ₗ[(quotientPresheaf φ).obj X] M)
    (h : ∀ (b : A.obj X ⧸ kernelIdeal φ X) (x : A.obj X),
      f (b ⊗ₜ[A.obj X] CommRingCat.KaehlerDifferential.d x) =
      g (b ⊗ₜ[A.obj X] CommRingCat.KaehlerDifferential.d x)) : f = g := by
  let := (a.app X).hom.toAlgebra
  have hω (ω : (differentialsPresheaf a).obj X) :
      ∀ b : A.obj X ⧸ kernelIdeal φ X, f (tmulOver φ a X b ω) = g (tmulOver φ a X b ω) := by
    have mem : ω ∈ Submodule.span (A.obj X)
        (Set.range (KaehlerDifferential.D (R.obj X) (A.obj X))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction mem using Submodule.span_induction with
    | mem x hx => obtain ⟨x, rfl⟩ := hx; exact fun b ↦ h b x
    | zero =>
        intro b
        exact (congrArg f (TensorProduct.tmul_zero _ b)).trans
          (((map_zero f).trans (map_zero g).symm).trans
            (congrArg g (TensorProduct.tmul_zero _ b)).symm)
    | add x y hx hy ihx ihy =>
        intro b
        refine (congrArg f (TensorProduct.tmul_add b x y)).trans ?_
        refine ((map_add f _ _).trans (congrArg₂ (· + ·) (ihx b) (ihy b))).trans ?_
        exact (map_add g _ _).symm.trans (congrArg g (TensorProduct.tmul_add b x y).symm)
    | smul r ω hω ih =>
        intro b
        exact (congrArg f (TensorProduct.smul_tmul r b ω).symm).trans
          ((ih (r • b)).trans (congrArg g (TensorProduct.smul_tmul r b ω)))
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero f).trans (map_zero g).symm
  | tmul b ω => exact hω ω b
  | add x y hx hy =>
      exact (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm)

/-- Relative differentials of the image presheaf. Its associated sheaf is
`Ω[B/R]`, since the image presheaf has associated sheaf `B` (Stacks 08TP). -/
noncomputable def quotientDifferentialsPresheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (a ≫ toQuotient φ)

/-- The canonical map from the conormal module to the tensor product on sections. -/
noncomputable def conormalToTensorApp (X : Cᵒᵖ) :
    (conormalPresheaf φ).obj X ⟶ (tensorPresheaf φ a).obj X := by
  let := (a.app X).hom.toAlgebra
  let I := kernelIdeal φ X
  let e := Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap (A.obj X) (A.obj X ⧸ I)))
    (Ideal.mk_ker.symm)
  let l := (KaehlerDifferential.kerCotangentToTensor (R.obj X) (A.obj X) (A.obj X ⧸ I)).comp
    e.toLinearMap
  exact ModuleCat.ofHom (X := (conormalPresheaf φ).obj X) (Y := (tensorPresheaf φ a).obj X)
    { toFun := l
      map_add' := map_add l
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact l.map_smul r x }

/-- On sections the conormal map sends the class of `f` to `1 ⊗ d f`. -/
@[simp]
lemma conormalToTensorApp_toCotangent (X : Cᵒᵖ) (x : kernelIdeal φ X) :
    conormalToTensorApp φ a X ((kernelIdeal φ X).toCotangent x) =
      (1 : A.obj X ⧸ kernelIdeal φ X) ⊗ₜ[A.obj X]
        CommRingCat.KaehlerDifferential.d (f := a.app X) x := by
  let := (a.app X).hom.toAlgebra
  simp [conormalToTensorApp]
  rfl

/-- The natural conormal-to-differentials map of presheaves. -/
noncomputable def conormalToTensor : conormalPresheaf φ ⟶ tensorPresheaf φ a where
  app := conormalToTensorApp φ a
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
    change conormalToTensorApp φ a Y ((kernelIdeal φ Y).toCotangent ⟨A.map f x, _⟩) =
      tensorMap φ a f (conormalToTensorApp φ a X ((kernelIdeal φ X).toCotangent x))
    rw [conormalToTensorApp_toCotangent, conormalToTensorApp_toCotangent]
    change (1 : A.obj Y ⧸ kernelIdeal φ Y) ⊗ₜ[A.obj Y] _ =
      (quotientPresheaf φ).map f 1 ⊗ₜ[A.obj Y]
        (differentialsPresheaf a).map f (CommRingCat.KaehlerDifferential.d x)
    rw [map_one ((quotientPresheaf φ).map f).hom]
    exact congrArg (fun ω : (differentialsPresheaf a).obj Y ↦
      (1 : A.obj Y ⧸ kernelIdeal φ Y) ⊗ₜ[A.obj Y] ω)
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a f x).symm

/-- The canonical base-change map on objectwise differentials. -/
noncomputable def tensorToDifferentialsApp (X : Cᵒᵖ) :
    (tensorPresheaf φ a).obj X ⟶ (quotientDifferentialsPresheaf φ a).obj X := by
  let := (a.app X).hom.toAlgebra
  exact ModuleCat.ofHom (X := (tensorPresheaf φ a).obj X)
    (Y := (quotientDifferentialsPresheaf φ a).obj X)
    (KaehlerDifferential.mapBaseChange
      (R.obj X) (A.obj X) ((quotientPresheaf φ).obj X))

/-- The base-change map sends `b ⊗ d x` to `b • d (x mod I)`. -/
@[simp]
lemma tensorToDifferentialsApp_tmul_d (X : Cᵒᵖ)
    (b : A.obj X ⧸ kernelIdeal φ X) (x : A.obj X) :
    tensorToDifferentialsApp φ a X
        (tmulOver φ a X b (CommRingCat.KaehlerDifferential.d x)) =
      b • CommRingCat.KaehlerDifferential.d (f := (a ≫ toQuotient φ).app X)
        (Ideal.Quotient.mk _ x) := by
  let := (a.app X).hom.toAlgebra
  exact (KaehlerDifferential.mapBaseChange_tmul _ _ _ _ _).trans
    (congrArg (b • ·) (KaehlerDifferential.map_D _ _ _ _ x))

/-- The natural right-hand map of the conormal sequence before sheafification. -/
noncomputable def tensorToDifferentials :
    tensorPresheaf φ a ⟶ quotientDifferentialsPresheaf φ a where
  app := tensorToDifferentialsApp φ a
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext φ a X
    intro b x
    change tensorToDifferentialsApp φ a Y
        (tmulOver φ a Y ((quotientPresheaf φ).map f b)
          ((differentialsPresheaf a).map f (CommRingCat.KaehlerDifferential.d x))) =
      (quotientDifferentialsPresheaf φ a).map f
        (tensorToDifferentialsApp φ a X
          (tmulOver φ a X b (CommRingCat.KaehlerDifferential.d x)))
    have hd : (differentialsPresheaf a).map f (CommRingCat.KaehlerDifferential.d x) =
        CommRingCat.KaehlerDifferential.d (f := a.app Y) (A.map f x) :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a f x
    rw [hd, tensorToDifferentialsApp_tmul_d, tensorToDifferentialsApp_tmul_d]
    have h2 : (quotientDifferentialsPresheaf φ a).map f
        (CommRingCat.KaehlerDifferential.d (f := (a ≫ toQuotient φ).app X)
          (Ideal.Quotient.mk (kernelIdeal φ X) x)) =
        CommRingCat.KaehlerDifferential.d (f := (a ≫ toQuotient φ).app Y)
          (Ideal.Quotient.mk (kernelIdeal φ Y) (A.map f x)) :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
        (a ≫ toQuotient φ) f (Ideal.Quotient.mk _ x)
    exact (congrArg (fun ω : (quotientDifferentialsPresheaf φ a).obj Y ↦
        (quotientPresheaf φ).map f b • ω) h2.symm).trans
      (PresheafOfModules.map_smul (quotientDifferentialsPresheaf φ a) f b _).symm

/-- Objectwise exactness over the image presheaf, by the ring conormal sequence. -/
lemma conormalToTensor_exact (X : Cᵒᵖ) :
    Function.Exact (conormalToTensorApp φ a X) (tensorToDifferentialsApp φ a X) := by
  let := (a.app X).hom.toAlgebra
  let I := kernelIdeal φ X
  let e := Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap (A.obj X) (A.obj X ⧸ I)))
    (Ideal.mk_ker.symm)
  have h := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    (R.obj X) (A.obj X) (A.obj X ⧸ I) Ideal.Quotient.mk_surjective
  refine fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (h x).mp hx
    refine ⟨e.symm z, ?_⟩
    change KaehlerDifferential.kerCotangentToTensor _ _ _ (e (e.symm z)) = x
    simpa only [e.apply_symm_apply] using hz
  · rintro ⟨z, rfl⟩
    exact (h _).mpr ⟨e z, rfl⟩

/-- The right-hand map over the image presheaf is objectwise surjective. -/
lemma tensorToDifferentials_surjective (X : Cᵒᵖ) :
    Function.Surjective (tensorToDifferentialsApp φ a X) := by
  let := (a.app X).hom.toAlgebra
  exact KaehlerDifferential.mapBaseChange_surjective
    (R.obj X) (A.obj X) (A.obj X ⧸ kernelIdeal φ X) Ideal.Quotient.mk_surjective

/-- The conormal complex over the image presheaf. -/
noncomputable def conormalPresheafComplex :
    ShortComplex (PresheafOfModules.{w} (quotientPresheaf φ ⋙ forget₂ _ RingCat)) :=
  .mk (conormalToTensor φ a) (tensorToDifferentials φ a) (by
    ext X x
    exact (conormalToTensor_exact φ a X _).mpr ⟨x, rfl⟩)

/-- Objectwise exactness implies exactness for a complex of presheaves of modules. -/
lemma presheafComplex_exact {S : Cᵒᵖ ⥤ RingCat.{w}}
    (K : ShortComplex (PresheafOfModules.{z} S))
    (h : ∀ X, Function.Exact (K.f.app X) (K.g.app X)) : K.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext X x
  have hX : (K.map (PresheafOfModules.evaluation S X)).Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (h X)
  have hz := (ShortComplex.exact_iff_isZero_homology _).mp hX
  exact ConcreteCategory.congr_hom
    ((IsZero.of_iso hz (K.mapHomologyIso (PresheafOfModules.evaluation S X)).symm).eq_of_src _ _) x

/-- The presheaf conormal complex is exact. -/
lemma conormalPresheafComplex_exact : (conormalPresheafComplex φ a).Exact :=
  presheafComplex_exact _ (conormalToTensor_exact φ a)

/-- The last map of the presheaf conormal complex is an epimorphism. -/
instance : Epi (conormalPresheafComplex φ a).g :=
  PresheafOfModules.epi_of_surjective (fun {X} ↦ tensorToDifferentials_surjective φ a X)

end Tensor

/-! ### Change of presentation along a commutative square

Let `φ₁ : A₁ ⟶ B₁` and `φ₂ : A₂ ⟶ B₂` be two presentations, and let `ψ : A₁ ⟶ A₂` and
`β : B₁ ⟶ B₂` satisfy `ψ ≫ φ₂ = φ₁ ≫ β`. Then `ψ` carries the kernel of `φ₁` into the kernel of
`φ₂` and hence induces maps between the terms of the two objectwise conormal sequences, those on
the differentials for a square of base rings `ρ : R₁ ⟶ R₂` over `ψ`. This is the general form of
the maps; the `…OfFac` family below is the case `β = 𝟙` of it.
-/

section ChangeOfPresentationSquare

variable {A₁ A₂ B₁ B₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (ψ : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (hsq : ψ ≫ φ₂ = φ₁ ≫ β)

include hsq in
/-- A commutative square carries the kernel of `φ₁` into the kernel of `φ₂`. -/
lemma kernelIdeal_le_comap_square (X : Cᵒᵖ) :
    kernelIdeal φ₁ X ≤ (kernelIdeal φ₂ X).comap (ψ.app X).hom := by
  intro x hx
  change φ₂.app X (ψ.app X x) = 0
  refine (congrArg (fun t : A₁ ⟶ B₂ ↦ (t.app X).hom x) hsq).trans ?_
  change β.app X (φ₁.app X x) = 0
  rw [show φ₁.app X x = 0 from hx, map_zero]

include hsq in
/-- The ring map `A₁(U)/I₁(U) → A₂(U)/I₂(U)` induced by a commutative square. -/
noncomputable def quotientMapOfSquare (X : Cᵒᵖ) :
    (quotientPresheaf φ₁).obj X ⟶ (quotientPresheaf φ₂).obj X :=
  CommRingCat.ofHom
    (Ideal.quotientMap _ (ψ.app X).hom (kernelIdeal_le_comap_square φ₁ φ₂ ψ β hsq X))

/-- The map `quotientMapOfSquare` sends the class of `x` to the class of `ψ x`. -/
@[simp]
lemma quotientMapOfSquare_mk (X : Cᵒᵖ) (x : A₁.obj X) :
    quotientMapOfSquare φ₁ φ₂ ψ β hsq X (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (ψ.app X x) := rfl

include hsq in
/-- The induced map on quotients is compatible with the inclusions into the targets. -/
lemma quotientToTarget_quotientMapOfSquare (X : Cᵒᵖ) (b : (quotientPresheaf φ₁).obj X) :
    (quotientToTarget φ₂).app X (quotientMapOfSquare φ₁ φ₂ ψ β hsq X b) =
      β.app X ((quotientToTarget φ₁).app X b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun t : A₁ ⟶ B₂ ↦ (t.app X).hom b) hsq

/-- The induced map on quotients commutes with the restriction maps. -/
lemma quotientMapOfSquare_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b : (quotientPresheaf φ₁).obj X) :
    quotientMapOfSquare φ₁ φ₂ ψ β hsq Y ((quotientPresheaf φ₁).map f b) =
      (quotientPresheaf φ₂).map f (quotientMapOfSquare φ₁ φ₂ ψ β hsq X b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk _ (ψ.app Y (A₁.map f b)) =
    Ideal.Quotient.mk _ (A₂.map f (ψ.app X b))
  exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂ Y)) (NatTrans.naturality_apply ψ f b)

/-- The induced map on conormal modules, semilinear over the induced map on quotients. -/
noncomputable abbrev conormalMapOfSquare (X : Cᵒᵖ) :
    (kernelIdeal φ₁ X).Cotangent →ₛₗ[(quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom]
      (kernelIdeal φ₂ X).Cotangent :=
  cotangentMap _ _ (ψ.app X).hom (kernelIdeal_le_comap_square φ₁ φ₂ ψ β hsq X)

/-- The induced map on conormal modules commutes with the restriction maps. -/
lemma conormalMapOfSquare_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (c : (conormalPresheaf φ₁).obj X) :
    conormalMapOfSquare φ₁ φ₂ ψ β hsq Y ((conormalPresheaf φ₁).map f c) =
      (conormalPresheaf φ₂).map f (conormalMapOfSquare φ₁ φ₂ ψ β hsq X c) := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  change (kernelIdeal φ₂ Y).toCotangent ⟨ψ.app Y (A₁.map f c), _⟩ =
    (kernelIdeal φ₂ Y).toCotangent ⟨A₂.map f (ψ.app X c), _⟩
  congr 1
  ext
  exact NatTrans.naturality_apply ψ f (c : A₁.obj X)

section Differentials

variable {R₁ R₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (ρ : R₁ ⟶ R₂)
  (ha : ρ ≫ a₂ = a₁ ≫ ψ)

include ha in
/-- The commutative square of rings on sections inducing the map on relative differentials. -/
lemma differentialsSquareOfSquare (X : Cᵒᵖ) :
    ρ.app X ≫ a₂.app X = a₁.app X ≫ ψ.app X :=
  congrArg (fun t : R₁ ⟶ A₂ ↦ t.app X) ha

include ha in
/-- The map `Ω[A₁(U)/R₁(U)] → Ω[A₂(U)/R₂(U)]` induced by a square of base rings over `ψ`,
semilinear over `ψ`. -/
noncomputable def differentialsMapOfSquare (X : Cᵒᵖ) :
    (differentialsPresheaf a₁).obj X →ₛₗ[(ψ.app X).hom] (differentialsPresheaf a₂).obj X where
  toFun := CommRingCat.KaehlerDifferential.map (g' := ψ.app X)
    (differentialsSquareOfSquare ψ a₁ a₂ ρ ha X)
  map_add' := map_add _
  map_smul' := (CommRingCat.KaehlerDifferential.map (g' := ψ.app X)
    (differentialsSquareOfSquare ψ a₁ a₂ ρ ha X)).hom.map_smul

/-- The map `differentialsMapOfSquare` sends `d x` to `d (ψ x)`. -/
@[simp]
lemma differentialsMapOfSquare_d (X : Cᵒᵖ) (x : A₁.obj X) :
    differentialsMapOfSquare ψ a₁ a₂ ρ ha X (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (ψ.app X x) :=
  CommRingCat.KaehlerDifferential.map_d (differentialsSquareOfSquare ψ a₁ a₂ ρ ha X) x

/-- Restriction of a universal differential is the universal differential of the restriction. -/
private lemma differentialsPresheaf_map_d {R A : Cᵒᵖ ⥤ CommRingCat.{w}} (a : R ⟶ A)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A.obj X) :
    (differentialsPresheaf a).map f (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (f := a.app Y) (A.map f x) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a f x

/-- The map on relative differentials commutes with the restriction maps. -/
lemma differentialsMapOfSquare_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfSquare ψ a₁ a₂ ρ ha Y ((differentialsPresheaf a₁).map f ω) =
      (differentialsPresheaf a₂).map f (differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω) := by
  change differentialsMapOfSquare ψ a₁ a₂ ρ ha Y ((differentialsPresheaf a₁).restrictₛₗ f ω) =
    (differentialsPresheaf a₂).restrictₛₗ f (differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω)
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      change differentialsMapOfSquare ψ a₁ a₂ ρ ha Y ((differentialsPresheaf a₁).map f
          (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)) =
        (differentialsPresheaf a₂).map f (differentialsMapOfSquare ψ a₁ a₂ ρ ha X
          (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x))
      rw [differentialsPresheaf_map_d, differentialsMapOfSquare_d, differentialsMapOfSquare_d,
        differentialsPresheaf_map_d]
      exact congrArg CommRingCat.KaehlerDifferential.d (NatTrans.naturality_apply ψ f x)
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih =>
      rw [map_smulₛₗ, map_smulₛₗ, ih, map_smulₛₗ, map_smulₛₗ]
      exact congrArg (fun s : A₂.obj Y ↦ s •
        (differentialsPresheaf a₂).restrictₛₗ f (differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω))
        (NatTrans.naturality_apply ψ f r)

include hsq in
/-- The induced map on quotients, as a map semilinear over `ψ`. -/
noncomputable def quotientMapOfSquareₛₗ (X : Cᵒᵖ) :
    (A₁.obj X ⧸ kernelIdeal φ₁ X) →ₛₗ[(ψ.app X).hom] (A₂.obj X ⧸ kernelIdeal φ₂ X) where
  toFun := quotientMapOfSquare φ₁ φ₂ ψ β hsq X
  map_add' := map_add (quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (ψ.app X (r * x)) =
      Ideal.Quotient.mk _ (ψ.app X r * ψ.app X x)
    exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂ X)) (map_mul (ψ.app X).hom r x)

/-- The induced map `(A₁/I₁) ⊗[A₁] Ω[A₁/R₁] → (A₂/I₂) ⊗[A₂] Ω[A₂/R₂]`, semilinear over
`ψ`. -/
noncomputable def tensorMapOfSquareₛₗ (X : Cᵒᵖ) :
    ((A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X))
      →ₛₗ[(ψ.app X).hom]
      ((A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗[A₂.obj X] ((differentialsPresheaf a₂).obj X)) :=
  TensorProduct.map (quotientMapOfSquareₛₗ φ₁ φ₂ ψ β hsq X)
    (differentialsMapOfSquare ψ a₁ a₂ ρ ha X)

/-- The induced map on the tensor product is semilinear over the induced map on `A₁/I₁`. -/
lemma tensorMapOfSquareₛₗ_smul (X : Cᵒᵖ) (r : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (x : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X (r • x) =
      quotientMapOfSquare φ₁ φ₂ ψ β hsq X r •
        tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    change tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X ((r * b) ⊗ₜ ω) =
      quotientMapOfSquare φ₁ φ₂ ψ β hsq X r •
        tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X (b ⊗ₜ ω)
    simp only [tensorMapOfSquareₛₗ, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    exact map_mul (quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom r b
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The induced map on the tensor product commutes with the restriction maps. -/
lemma tensorMapOfSquareₛₗ_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha Y (tensorMapₛₗ φ₁ a₁ f x) =
      tensorMapₛₗ φ₂ a₂ f (tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b ω =>
    refine (congrArg (tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha Y)
      (TensorProduct.map_tmul _ _ b ω)).trans ?_
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (tensorMapₛₗ φ₂ a₂ f)
      (TensorProduct.map_tmul _ _ b ω)).symm
    refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
    exact congrArg₂ (fun b (ω : (differentialsPresheaf a₂).obj Y) ↦ b ⊗ₜ[A₂.obj Y] ω)
      (quotientMapOfSquare_naturality φ₁ φ₂ ψ β hsq f b)
      (differentialsMapOfSquare_naturality ψ a₁ a₂ ρ ha f ω)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end Differentials

end ChangeOfPresentationSquare

/-! ### Change of presentation

Let `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ B` be two presentations of `B`, and let `ψ : A₁ ⟶ A₂` be a
factorisation of `φ₁` through `φ₂`. Then `ψ` carries the kernel of `φ₁` into the kernel of `φ₂`
and hence induces maps between the terms of the two objectwise conormal sequences.
-/

section ChangeOfPresentation

variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁)

include hψ in
/-- A factorisation `ψ ≫ φ₂ = φ₁` carries the kernel of `φ₁` into the kernel of `φ₂`. -/
lemma kernelIdeal_le_comap (X : Cᵒᵖ) :
    kernelIdeal φ₁ X ≤ (kernelIdeal φ₂ X).comap (ψ.app X).hom :=
  kernelIdeal_le_comap_square φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X

include hψ in
/-- The ring map `A₁(U)/I₁(U) → A₂(U)/I₂(U)` induced by a factorisation. -/
noncomputable def quotientMapOfFac (X : Cᵒᵖ) :
    (quotientPresheaf φ₁).obj X ⟶ (quotientPresheaf φ₂).obj X :=
  quotientMapOfSquare φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X

/-- The map `quotientMapOfFac` sends the class of `x` to the class of `ψ x`. -/
@[simp]
lemma quotientMapOfFac_mk (X : Cᵒᵖ) (x : A₁.obj X) :
    quotientMapOfFac φ₁ φ₂ ψ hψ X (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (ψ.app X x) :=
  quotientMapOfSquare_mk φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X x

/-- The induced map on quotients is compatible with the inclusions into the target. -/
lemma quotientToTarget_quotientMapOfFac (X : Cᵒᵖ)
    (b : (quotientPresheaf φ₁).obj X) :
    (quotientToTarget φ₂).app X (quotientMapOfFac φ₁ φ₂ ψ hψ X b) =
      (quotientToTarget φ₁).app X b := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun t : A₁ ⟶ B ↦ (t.app X).hom b) hψ

/-- The induced map on quotients commutes with the restriction maps. -/
lemma quotientMapOfFac_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b : (quotientPresheaf φ₁).obj X) :
    quotientMapOfFac φ₁ φ₂ ψ hψ Y ((quotientPresheaf φ₁).map f b) =
      (quotientPresheaf φ₂).map f (quotientMapOfFac φ₁ φ₂ ψ hψ X b) :=
  quotientMapOfSquare_naturality φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) f b

/-- The induced map on conormal modules, semilinear over the induced map on quotients. -/
noncomputable abbrev conormalMapOfFac (X : Cᵒᵖ) :
    (kernelIdeal φ₁ X).Cotangent →ₛₗ[(quotientMapOfFac φ₁ φ₂ ψ hψ X).hom]
      (kernelIdeal φ₂ X).Cotangent :=
  conormalMapOfSquare φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X

/-- The induced map on conormal modules commutes with the restriction maps. -/
lemma conormalMapOfFac_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (c : (conormalPresheaf φ₁).obj X) :
    conormalMapOfFac φ₁ φ₂ ψ hψ Y ((conormalPresheaf φ₁).map f c) =
      (conormalPresheaf φ₂).map f (conormalMapOfFac φ₁ φ₂ ψ hψ X c) :=
  conormalMapOfSquare_naturality φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) f c

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (ha : a₁ ≫ ψ = a₂)

include ha in
/-- The commutative square of rings inducing the map on relative differentials. -/
lemma differentialsSquare (X : Cᵒᵖ) :
    𝟙 (R.obj X) ≫ a₂.app X = a₁.app X ≫ ψ.app X :=
  (Category.id_comp (a₂.app X)).trans (congrArg (fun t : R ⟶ A₂ ↦ t.app X) ha).symm

include ha in
/-- The map `Ω[A₁(U)/R(U)] → Ω[A₂(U)/R(U)]` induced by `ψ`, semilinear over `ψ`. -/
noncomputable def differentialsMapOfFac (X : Cᵒᵖ) :
    (differentialsPresheaf a₁).obj X →ₛₗ[(ψ.app X).hom] (differentialsPresheaf a₂).obj X :=
  differentialsMapOfSquare ψ a₁ a₂ (𝟙 R) (by simpa using ha.symm) X

/-- The map `differentialsMapOfFac` sends `d x` to `d (ψ x)`. -/
@[simp]
lemma differentialsMapOfFac_d (X : Cᵒᵖ) (x : A₁.obj X) :
    differentialsMapOfFac ψ a₁ a₂ ha X (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (ψ.app X x) :=
  differentialsMapOfSquare_d ψ a₁ a₂ (𝟙 R) (by simpa using ha.symm) X x

/-- The map on relative differentials commutes with the restriction maps. -/
lemma differentialsMapOfFac_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfFac ψ a₁ a₂ ha Y ((differentialsPresheaf a₁).map f ω) =
      (differentialsPresheaf a₂).map f (differentialsMapOfFac ψ a₁ a₂ ha X ω) :=
  differentialsMapOfSquare_naturality ψ a₁ a₂ (𝟙 R) (by simpa using ha.symm) f ω

include hψ in
/-- The induced map on quotients, as a map semilinear over `ψ`. -/
noncomputable def quotientMapOfFacₛₗ (X : Cᵒᵖ) :
    (A₁.obj X ⧸ kernelIdeal φ₁ X) →ₛₗ[(ψ.app X).hom] (A₂.obj X ⧸ kernelIdeal φ₂ X) :=
  quotientMapOfSquareₛₗ φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X

/-- The induced map `(A₁/I₁) ⊗[A₁] Ω[A₁/R] → (A₂/I₂) ⊗[A₂] Ω[A₂/R]`, semilinear
over `ψ`. -/
noncomputable def tensorMapOfFacₛₗ (X : Cᵒᵖ) :
    ((A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X))
      →ₛₗ[(ψ.app X).hom]
      ((A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗[A₂.obj X] ((differentialsPresheaf a₂).obj X)) :=
  TensorProduct.map (quotientMapOfFacₛₗ φ₁ φ₂ ψ hψ X) (differentialsMapOfFac ψ a₁ a₂ ha X)

/-- The induced map on the tensor product is semilinear over the induced map on `A₁/I₁`. -/
lemma tensorMapOfFacₛₗ_smul (X : Cᵒᵖ) (r : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (x : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X (r • x) =
      quotientMapOfFac φ₁ φ₂ ψ hψ X r • tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X x :=
  tensorMapOfSquareₛₗ_smul φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) a₁ a₂ (𝟙 R)
    (by simpa using ha.symm) X r x

/-- The induced map on the tensor product commutes with the restriction maps. -/
lemma tensorMapOfFacₛₗ_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha Y (tensorMapₛₗ φ₁ a₁ f x) =
      tensorMapₛₗ φ₂ a₂ f (tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X x) :=
  tensorMapOfSquareₛₗ_naturality φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) a₁ a₂ (𝟙 R)
    (by simpa using ha.symm) f x

end ChangeOfPresentation

end Stacks.Sites.Conormal
