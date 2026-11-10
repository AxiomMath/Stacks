module

public import Mathlib.CategoryTheory.Elements
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Testing smoothness on small extensions, and smoothness of set-valued functors

Two reductions of the smoothness lifting property for a morphism of categories cofibered in
groupoids over `𝒞_Λ`.

First, smoothness need only be tested on small extensions (Stacks 06HH): every surjection in
`𝒞_Λ` is a finite composite of small extensions followed by an isomorphism, and the lifting
property propagates along such a chain because in a category cofibered in groupoids a morphism
lying over an isomorphism is an isomorphism and a morphism lying over a composite factors.

Second, for categories cofibered in sets — that is, for categories of elements of set-valued
functors — the categorical lifting condition is Schlessinger's elementwise surjectivity
condition onto the fibre product (Stacks 06HJ).

## Main results

* `Deformation.isSmooth_of_lifts_smallExtensions`: the lifting property for small extensions
  implies smoothness.
* `Deformation.isSmooth_elementsBasedFunctor_iff`: for a natural transformation of set-valued
  functors, smoothness of the induced morphism of categories of elements is surjectivity of
  the usual map to the fibre product.

## Implementation notes

Categories over the base and their morphisms are represented by Mathlib's `BasedCategory` and
`BasedFunctor`, and a small extension is a condition on the underlying morphism of bundled
commutative rings, as for Stacks 02HS. The factorization of a surjection into small extensions
has a target only isomorphic to the target of the given morphism, so the chain induction is
preceded by a transport along that isomorphism, which uses only cofiberedness of the source.

A set-valued functor is represented by its category of elements and a natural transformation
by the induced based functor; surjectivity onto the fibre product is written elementwise,
including the equality that defines that fibre product, because the category of elements has
no chosen fibre products.

## References

* [Stacks Project, Tag 06HH](https://stacks.math.columbia.edu/tag/06HH)
* [Stacks Project, Tag 06HJ](https://stacks.math.columbia.edu/tag/06HJ)
-/

@[expose] public section

namespace Deformation

/-! ### Testing smoothness on small extensions -/

section
open CategoryTheory InfinitesimalLifting
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The source of a morphism into `φ.obj x` lying over `f` lies over the codomain of `f`. -/
private theorem obj_eq_of_isHomLift
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} {f : B ⟶ A}
    {y : 𝓖.obj} {x : 𝓕.obj} {g : y ⟶ φ.obj x} (hg : 𝓖.p.IsHomLift f g) : 𝓕.p.obj x = A :=
  (BasedFunctor.w_obj φ x).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)

/-- The inverse of an isomorphism lying over `e.hom` lies over `e.inv`. -/
private theorem isHomLift_inv_of_iso {C E : Type*} [Category C] [Category E] (p : E ⥤ C)
    {B A : C} (e : B ≅ A) {a b : E} (g : a ⟶ b) [IsIso g] (hg : p.IsHomLift e.hom g) :
    p.IsHomLift e.inv (inv g) := by
  simpa using IsHomLift.inv p e.hom g

/-- Lifting an isomorphism of the base to `x` gives a lift whose image under `φ` is an
isomorphism lying over it. -/
private theorem exists_isHomLift_map_of_iso
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (φ : BasedFunctor 𝓕 𝓖)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : B ≅ A) {x : 𝓕.obj} (hx : 𝓕.p.obj x = A) :
    ∃ (x' : 𝓕.obj) (ell : x' ⟶ x), 𝓕.p.IsHomLift e.hom ell ∧
      𝓖.p.IsHomLift e.hom (φ.map ell) ∧ IsIso (φ.map ell) := by
  obtain ⟨x', ell, hell, hiso⟩ := exists_isHomLift_of_iso h𝓕 e (x := x) hx
  let _ : IsIso ell := hiso
  refine ⟨x', ell, hell, ?_, inferInstance⟩
  let _ : 𝓕.p.IsHomLift e.hom ell := hell
  infer_instance

/-- Solving a lifting problem over an isomorphism of the base. -/
private theorem lift_iso {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : B ≅ A) (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x)
    (hg : 𝓖.p.IsHomLift e.hom g) :
    ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
      𝓕.p.IsHomLift e.hom lift ∧
        𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map lift = a ≫ g := by
  obtain ⟨x', lift, hlift, hφlift, -⟩ :=
    exists_isHomLift_map_of_iso h𝓕 φ e (obj_eq_of_isHomLift φ hg)
  have hgiso : IsIso g := by
    have hmapiso : IsIso (𝓖.p.map g) := by
      rw [IsHomLift.fac' 𝓖.p e.hom g]
      infer_instance
    exact isIso_of_isIso_map h𝓖 g
  refine ⟨x', lift, φ.map lift ≫ inv g, hlift, ?_, by simp [Category.assoc]⟩
  simpa using isHomLift_comp hφlift (isHomLift_inv_of_iso 𝓖.p e g hg)

/-- The lifting property propagates along a chain of small extensions. -/
private theorem lift_chain
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (h : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x),
          𝓖.p.IsHomLift f g →
            ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
              𝓕.p.IsHomLift f lift ∧
                𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map lift = a ≫ g)
    {n : ℕ} (D : ComposableArrows (ArtinianLocalAlgCat.{u, v, w} Λ k) n)
    (hsmall : ∀ (i : ℕ) (hi : i < n),
      IsSmallExtension (CommRingCat.ofHom (D.map' i (i + 1)).hom.toRingHom)) :
    ∀ (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x),
      𝓖.p.IsHomLift D.hom g →
        ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
          𝓕.p.IsHomLift D.hom lift ∧
            𝓖.p.IsHomLift (𝟙 D.left) a ∧ φ.map lift = a ≫ g := by
  induction n with
  | zero =>
      intro y x g hg
      let _ : 𝓖.p.IsHomLift D.hom g := hg
      have hgid : 𝓖.p.IsHomLift (𝟙 D.left) g := by
        convert hg using 1
        simp [ComposableArrows.hom, ComposableArrows.left]
      let _ : IsIso g := isIso_of_isHomLift_id h𝓖 g hgid
      have hx : 𝓕.p.obj x = D.left := (obj_eq_of_isHomLift φ hg).trans (by simp)
      have hlift : 𝓕.p.IsHomLift D.hom (𝟙 x) := by
        convert (IsHomLift.id hx : 𝓕.p.IsHomLift (𝟙 D.left) (𝟙 x)) using 1
        simp [ComposableArrows.hom, ComposableArrows.left, ComposableArrows.right]
      exact ⟨x, 𝟙 x, inv g, hlift, IsHomLift.lift_id_inv_isIso _ _ g, by simp⟩
  | succ n ih =>
      intro y x g hg
      let f := D.map' 0 1
      let E := D.δ₀
      have htail : ∀ (i : ℕ) (hi : i < n),
          IsSmallExtension (CommRingCat.ofHom (E.map' i (i + 1)).hom.toRingHom) :=
        fun i hi => hsmall (i + 1) (by omega)
      have hh : D.hom = f ≫ E.hom := D.map'_comp 0 1 (n + 1)
      obtain ⟨y', q, r, hq, hr, hqr⟩ :=
        exists_factor_of_isHomLift_comp h𝓖 f E.hom g (hh ▸ hg)
      obtain ⟨x₀, l₀, a₀, hl₀, ha₀, hφ₀⟩ := ih E htail y' x r hr
      let _ : IsIso a₀ := isIso_of_isHomLift_id h𝓖 a₀ ha₀
      let g₀ := q ≫ inv a₀
      have hg₀ : 𝓖.p.IsHomLift f g₀ := by
        let _ : 𝓖.p.IsHomLift f q := hq
        let _ : 𝓖.p.IsHomLift (𝟙 E.left) (inv a₀) := IsHomLift.lift_id_inv_isIso _ _ a₀
        exact IsHomLift.comp_lift_id_right' 𝓖.p f q E.left (inv a₀)
      obtain ⟨x₁, l₁, a₁, hl₁, ha₁, hφ₁⟩ := h f (hsmall 0 (by omega)) y x₀ g₀ hg₀
      refine ⟨x₁, l₁ ≫ l₀, a₁, ?_, ha₁, ?_⟩
      · exact hh.symm ▸ isHomLift_comp hl₁ hl₀
      · simp [Functor.map_comp, hφ₁, hφ₀, g₀, Category.assoc, hqr]

/-- For a morphism of categories cofibered in groupoids, the lifting property
for small extensions implies the lifting property for every surjective morphism,
and hence smoothness. -/
@[stacks 06HH, sga "7 VI 2.2(a)" "(iii) => (i)"]
theorem isSmooth_of_lifts_smallExtensions
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (h : ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ (y : 𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x),
          𝓖.p.IsHomLift f g →
            ∃ (x' : 𝓕.obj) (lift : x' ⟶ x) (a : φ.obj x' ⟶ y),
              𝓕.p.IsHomLift f lift ∧
                𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map lift = a ≫ g) :
    IsSmooth φ := by
  intro B A f hf y x g hg
  obtain ⟨n, D, rfl, e, hfactor, hsmall⟩ := surjective_factors_into_smallExtensions f hf
  cases n with
  | zero =>
      have hLR : D.left = D.right := rfl
      let e' : D.left ≅ A := (eqToIso hLR).trans e
      have hDhom : D.hom = (eqToIso hLR).hom := by
        apply ArtinianLocalAlgCat.hom_ext
        ext a
        simp [ComposableArrows.hom, AlgHom.id]
        rfl
      have hfeq : e'.hom = f := by
        calc
          e'.hom = (eqToIso hLR).hom ≫ e.hom := by simp [e']
          _ = D.hom ≫ e.hom := by rw [hDhom]
          _ = f := by
            simpa [ComposableArrows.hom, eqToHom_refl, Category.id_comp] using hfactor
      have hge : 𝓖.p.IsHomLift e'.hom g := hfeq.symm ▸ hg
      obtain ⟨x', lift, a, hlift, ha, hφ⟩ := lift_iso h𝓕 h𝓖 φ e' y x g hge
      exact ⟨x', lift, a, hfeq ▸ hlift, ha, hφ⟩
  | succ n =>
      have hfactor' : D.hom ≫ e.hom = f := by
        simpa [eqToHom_refl, Category.id_comp] using hfactor
      have hgf : 𝓖.p.IsHomLift (D.hom ≫ e.hom) g := hfactor'.symm ▸ hg
      obtain ⟨x', ell, hell, hφell, _⟩ :=
        exists_isHomLift_map_of_iso h𝓕 φ e (obj_eq_of_isHomLift φ hg)
      let g' := g ≫ inv (φ.map ell)
      have hg' : 𝓖.p.IsHomLift D.hom g' := by
        simpa [g', Category.assoc] using isHomLift_comp hgf (isHomLift_inv_of_iso 𝓖.p e _ hφell)
      obtain ⟨x₀, lift₀, a, hlift₀, ha, hφ₀⟩ := lift_chain h𝓖 φ h D hsmall y x' g' hg'
      have hfinal : 𝓕.p.IsHomLift (D.hom ≫ e.hom) (lift₀ ≫ ell) :=
        isHomLift_comp hlift₀ hell
      refine ⟨x₀, lift₀ ≫ ell, a, hfactor' ▸ hfinal, ha, ?_⟩
      calc
        φ.map (lift₀ ≫ ell) = φ.map lift₀ ≫ φ.map ell := φ.map_comp _ _
        _ = (a ≫ g') ≫ φ.map ell := by rw [hφ₀]
        _ = a ≫ g := by simp [g', Category.assoc]

end

/-! ### Smooth morphisms of set-valued functors -/

section
open CategoryTheory
universe u v w t

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Smoothness of a morphism between categories of elements is equivalent to
surjectivity of the usual map to the fibre product for every surjection in
`𝒞_Λ`. -/
@[stacks 06HJ]
theorem isSmooth_elementsBasedFunctor_iff
    {F G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t} (α : F ⟶ G) :
    IsSmooth (elementsBasedFunctor α) ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A),
        Function.Surjective f.hom →
          ∀ (xA : F.obj A) (yB : G.obj B),
            α.app A xA = G.map f yB →
            ∃ xB : F.obj B, F.map f xB = xA ∧ α.app B xB = yB := by
  constructor
  · intro h B A f hf xA yB hxy
    let _ : Category F.Elements := (BasedCategory.ofFunctor (Functor.Elements.π F)).category
    let _ : Category G.Elements := (BasedCategory.ofFunctor (Functor.Elements.π G)).category
    let x : F.Elements := F.elementsMk A xA
    let y : G.Elements := G.elementsMk B yB
    let g : y ⟶ (NatTrans.mapElements α).obj x := Functor.Elements.homMk f hxy.symm
    have hg : ((BasedCategory.ofFunctor (Functor.Elements.π G)).p).IsHomLift f g := by
      simpa [g, BasedCategory.ofFunctor] using
        IsHomLift.map (BasedCategory.ofFunctor (Functor.Elements.π G)).p g
    obtain ⟨x', h', a, hh, ha, -⟩ := h f hf y x g hg
    obtain @⟨B', xB⟩ := x'
    have hxbase : B' = B := by
      let _ := hh
      simpa [BasedCategory.ofFunctor, Functor.Elements.π] using
        IsHomLift.domain_eq
          (p := (BasedCategory.ofFunctor (Functor.Elements.π F)).p) f h'
    cases hxbase.symm
    have hbase : 𝟙 B = (Functor.Elements.π G).map a := by
      simpa [BasedCategory.ofFunctor, Functor.Elements.π] using
        (@IsHomLift.eq_of_isHomLift _ _
          (BasedCategory.ofFunctor (Functor.Elements.π G)).category inferInstance
          (BasedCategory.ofFunctor (Functor.Elements.π G)).p
          ((NatTrans.mapElements α).obj (F.elementsMk B xB)) y (𝟙 B) a ha)
    refine ⟨xB, ?_, ?_⟩
    · have hmap : f = (Functor.Elements.π F).map h' := by
        simpa [BasedCategory.ofFunctor, Functor.Elements.π] using
          (@IsHomLift.eq_of_isHomLift _ _
            (BasedCategory.ofFunctor (Functor.Elements.π F)).category inferInstance
            (BasedCategory.ofFunctor (Functor.Elements.π F)).p
            (F.elementsMk B xB) x f h' hh)
      simpa [Functor.Elements.π, hmap] using h'.map_val
    · have haVal : a.hom = 𝟙 B := by simpa [Functor.Elements.π] using hbase.symm
      simpa [y, haVal, NatTrans.mapElements, Functor.map_id_apply] using a.map_val
  · intro h
    dsimp [IsSmooth, elementsBasedFunctor]
    intro B A f hf
    let _ : Category F.Elements := inferInstance
    let _ : Category G.Elements := inferInstance
    intro y x g hg
    obtain @⟨B', yB⟩ := y; obtain @⟨A', xA⟩ := x
    let _ := hg
    have hdom : B' = B := by
      simpa [BasedCategory.ofFunctor, Functor.Elements.π] using
        IsHomLift.domain_eq
          (p := (BasedCategory.ofFunctor (Functor.Elements.π G)).p) f g
    have hcod : A' = A := by
      simpa [BasedCategory.ofFunctor, Functor.Elements.π, NatTrans.mapElements] using
        IsHomLift.codomain_eq
          (p := (BasedCategory.ofFunctor (Functor.Elements.π G)).p) f g
    cases hdom.symm; cases hcod.symm
    have hval : g.hom = f := by
      simpa [BasedCategory.ofFunctor, Functor.Elements.π] using
        (@IsHomLift.eq_of_isHomLift _ _
          (BasedCategory.ofFunctor (Functor.Elements.π G)).category inferInstance
          (BasedCategory.ofFunctor (Functor.Elements.π G)).p
          (G.elementsMk B yB) ((NatTrans.mapElements α).obj (F.elementsMk A xA)) f g hg).symm
    obtain ⟨xB, hxB, hyB⟩ := h f hf xA yB (by
      simpa [hval, NatTrans.mapElements] using g.map_val.symm)
    refine ⟨F.elementsMk B xB, Functor.Elements.homMk f hxB, Functor.Elements.homMk (𝟙 B) ?_,
      ?_, ?_, ?_⟩
    · simpa [NatTrans.mapElements, Functor.map_id_apply] using hyB
    · exact IsHomLift.of_fac (BasedCategory.ofFunctor (Functor.Elements.π F)).p f
        (Functor.Elements.homMk (x := F.elementsMk B xB) (y := F.elementsMk A xA) f hxB) rfl rfl rfl
    · exact IsHomLift.of_fac (BasedCategory.ofFunctor (Functor.Elements.π G)).p (𝟙 B)
        (Functor.Elements.homMk (x := G.elementsMk B (α.app B xB)) (y := G.elementsMk B yB)
          (𝟙 B) (by simpa [NatTrans.mapElements, Functor.map_id_apply] using hyB))
        rfl rfl rfl
    · apply Functor.Elements.hom_ext
      change f = (𝟙 B) ≫ g.hom
      simp [hval]

end

end Deformation

end
