module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.Examples.Linear.FiniteProjectiveCofibered
public import StacksFrontier.Deformation.Examples.Linear.ModulePatching
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Finite projective modules satisfy the Rim–Schlessinger condition

The category of finite projective modules over the objects of `𝒞_Λ` satisfies condition (RS):
given `(A₁, M₁) → (A, M)` and `(A₂, M₂) → (A, M)` with `A₂ → A` surjective, the fibre product
`A₁ ×_A A₂` carries a finite projective module patching `M₁` and `M₂` along `M`, by Milnor
patching, and the resulting square is a pullback square both upstairs and downstairs.
Consequently the deformations of a finite-dimensional vector space form a deformation category.

## Main results

* `Deformation.Examples.FiniteProjectiveModule.Family.satisfiesRS_projection`: condition (RS)
  for the projection of any family of finite projective modules.
* `Deformation.Examples.FiniteProjectiveModule.isDeformationCategory_deformationCategory`: the
  deformations of a finite-dimensional `k`-vector space form a deformation category.

## Implementation notes

The fibre product object of `𝒞_Λ` is `Deformation.ArtinianLocalAlgCat.pullbackObj_of_surjective`
and the module patching it is `Deformation.Examples.exists_finiteProjectiveModulePatch`; the two
speak of the algebra fibre product and the ring fibre product respectively, and
`Deformation.Examples.ringPullbackEquivAlgPullback` identifies them.

Every part of the construction whose statement does not mention the patched object itself is a
separate declaration above; what remains in `Family.satisfiesRS_projection` is the assembly of
the base fibre product, the Milnor patch and the two morphisms out of it.

The deformation-category statement is about the slice over the special-fibre object `(k, V)`,
whose base algebra has carrier `k`, while the fibre defining a predeformation category is taken
over `Deformation.residueFieldObject`, whose carrier is `ULift k`. The two are compared by
`Deformation.Examples.residueFieldBaseIso`, lifted to the module categories by cofiberedness,
and the slice categories are compared by `Deformation.Examples.isDeformationCategory_comp`
applied to `Over.map`.

## References

* [Stacks Project, Tag 0DVP](https://stacks.math.columbia.edu/tag/0DVP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace Deformation.Examples.FiniteProjectiveModule

universe u v w t u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The morphism of finite projective modules determined by a morphism of base algebras
together with an identification of the extension of scalars. -/
private noncomputable def homOfBaseChange
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (f : X.base ⟶ Y.base)
    (e : letI : Algebra X.base Y.base := f.hom.toRingHom.toAlgebra
      TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier) :
    FiniteProjectiveModule.Hom X Y := by
  letI : Algebra X.base Y.base := f.hom.toRingHom.toAlgebra
  refine ⟨f, ?_, ⟨e, ?_⟩⟩
  · refine
      { toFun := fun m => e (TensorProduct.tmul X.base (1 : Y.base) m)
        map_add' := by
          intro m n
          rw [TensorProduct.tmul_add, map_add]
        map_smul' := ?_ }
    intro a m
    change e (TensorProduct.tmul X.base (1 : Y.base) (a • m)) =
      f.hom a • e (TensorProduct.tmul X.base (1 : Y.base) m)
    rw [TensorProduct.tmul_smul]
    change e ((algebraMap X.base Y.base a) •
      TensorProduct.tmul X.base (1 : Y.base) m) = _
    rw [e.map_smul]
    rfl
  · intro m
    rfl

/-- The semilinear map of `homOfBaseChange` is `m ↦ e (1 ⊗ m)`. -/
private theorem homOfBaseChange_linear
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (f : X.base ⟶ Y.base) (A : Algebra X.base Y.base)
    (h : A = f.hom.toRingHom.toAlgebra)
    (e : letI := A; TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier)
    (m : X.carrier) :
    (homOfBaseChange f (h ▸ e)).linear m =
      e (@TensorProduct.tmul X.base _ Y.base X.carrier _ _ A.toModule _ 1 m) := by
  cases h
  rfl

/-- The morphism of finite projective modules determined by a morphism `f` of base algebras
together with an identification of the extension of scalars along a ring homomorphism `g` that
is equal to the one underlying `f`. Stating the identification for `g` rather than for
`f.hom.toRingHom` lets the caller keep whichever of the two descriptions it has. -/
private noncomputable def homOfBaseChange'
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (f : X.base ⟶ Y.base) (g : X.base →+* Y.base) (hg : g = f.hom.toRingHom)
    (e : letI : Algebra X.base Y.base := g.toAlgebra
      TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier) :
    FiniteProjectiveModule.Hom X Y := by
  subst hg
  exact homOfBaseChange f e

/-- Its base morphism is `f`. -/
private theorem homOfBaseChange'_base
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (f : X.base ⟶ Y.base) (g : X.base →+* Y.base) (hg : g = f.hom.toRingHom)
    (e : letI : Algebra X.base Y.base := g.toAlgebra
      TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier) :
    (homOfBaseChange' f g hg e).base = f := by
  subst hg
  rfl

/-- Its semilinear map is `m ↦ e (1 ⊗ m)`. -/
private theorem homOfBaseChange'_linear
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (f : X.base ⟶ Y.base) (g : X.base →+* Y.base) (hg : g = f.hom.toRingHom)
    (e : letI : Algebra X.base Y.base := g.toAlgebra
      TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier) (m : X.carrier) :
    letI : Algebra X.base Y.base := g.toAlgebra
    (homOfBaseChange' f g hg e).linear m =
      e (TensorProduct.tmul X.base (1 : Y.base) m) := by
  subst hg
  rfl

/-- The base-change datum of a morphism, read along a ring homomorphism equal to its
underlying one. -/
private theorem baseChange_of_ringHom_eq
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (g : FiniteProjectiveModule.Hom X Y)
    (f : X.base →+* Y.base) (h : g.base.hom.toRingHom = f) :
    letI : Algebra X.base Y.base := f.toAlgebra
    ∃ e : TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier,
      ∀ m, e (TensorProduct.tmul X.base (1 : Y.base) m) = g.linear m := by
  subst f
  exact g.baseChange

/-- The underlying algebra map of `eqToHom` is injective. -/
private theorem eqToHom_hom_injective
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) :
    Function.Injective (eqToHom h).hom := by
  cases h
  intro a b hab
  exact hab

namespace Family

/-- If the projection of a morphism is surjective, so is the base morphism it corresponds
to. -/
private theorem homEquiv_base_surjective
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    ∀ {X₂ X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)} (f₂ : X₂ ⟶ X),
      Function.Surjective (𝓕.projection.map f₂).hom →
        Function.Surjective (𝓕.homEquiv X₂ X f₂).base.hom := by
  let := 𝓕.category
  intro X₂ X f₂ hsurj
  let h := 𝓕.homEquiv X₂ X f₂
  have hsurj' : Function.Surjective
      ((eqToHom (𝓕.projection_obj X).symm).hom.comp
        (h.base.hom.comp (eqToHom (𝓕.projection_obj X₂)).hom)) := by
    simpa [𝓕.projection_map_eq f₂, ArtinianLocalAlgCat.comp_hom, Function.comp_def] using hsurj
  have hsurj₂ : Function.Surjective
      (h.base.hom.comp (eqToHom (𝓕.projection_obj X₂)).hom) :=
    Function.Surjective.of_comp_left hsurj' (eqToHom_hom_injective (𝓕.projection_obj X).symm)
  exact Function.Surjective.of_comp hsurj₂

end Family

/-- The pushforward of an object along a morphism of the base, with the identification of its
image written as a commuting triangle. -/
private lemma exists_pushforward_eq {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (p : C ⥤ D)
    (hp : IsCofiberedInGroupoids p) (X : C) (B : D) (f : p.obj X ⟶ B) :
    ∃ (Y : C) (a : X ⟶ Y) (hY : p.obj Y = B), p.map a ≫ eqToHom hY = f := by
  obtain ⟨Y, a, hY, hlift⟩ := exists_pushforward_codomain hp (rfl : p.obj X = p.obj X) f
  refine ⟨Y, a, hY, ?_⟩
  let := hlift
  have hh := IsHomLift.fac' p f a
  simp [hh]

/-- A cone over a cospan in a category cofibered in groupoids whose image is a limit cone is
itself a limit cone, once every competing cone maps into it and the map is unique. The two
hypotheses are what the cofibered condition reduces the universal property to: a competing cone
is first pushed forward to lie over the apex of `c`. -/
private theorem cofibered_pullback_isLimit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (p : C ⥤ D) (hp : IsCofiberedInGroupoids p)
    {X₁ X₂ X : C} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (c : PullbackCone f₁ f₂) (hpc : IsLimit (c.map p))
    (hex : ∀ (Y : C) (a : Y ⟶ X₁) (b : Y ⟶ X₂), a ≫ f₁ = b ≫ f₂ →
      ∀ hY : p.obj Y = p.obj c.pt,
      p.map a = eqToHom hY ≫ p.map c.fst →
      p.map b = eqToHom hY ≫ p.map c.snd →
      ∃ l : Y ⟶ c.pt, l ≫ c.fst = a ∧ l ≫ c.snd = b)
    (huniq : ∀ {Y : C} (a b : Y ⟶ c.pt), a ≫ c.fst = b ≫ c.fst →
      a ≫ c.snd = b ≫ c.snd → a = b) : Nonempty (IsLimit c) := by
  have hlift (d : PullbackCone f₁ f₂) :
      ∃ l : d.pt ⟶ c.pt, l ≫ c.fst = d.fst ∧ l ≫ c.snd = d.snd := by
    let f : p.obj d.pt ⟶ p.obj c.pt := hpc.lift (d.map p)
    have hf₁ : f ≫ p.map c.fst = p.map d.fst := hpc.fac (d.map p) WalkingCospan.left
    have hf₂ : f ≫ p.map c.snd = p.map d.snd := hpc.fac (d.map p) WalkingCospan.right
    obtain ⟨Y, a, hY, ha⟩ := exists_pushforward_eq p hp d.pt (p.obj c.pt) f
    obtain ⟨b₁, ⟨hb₁, hab₁⟩, _⟩ := existsUnique_factor_of_isHomLift hp a d.fst
      (eqToHom hY ≫ p.map c.fst) (by rw [← Category.assoc, ha, hf₁])
    obtain ⟨b₂, ⟨hb₂, hab₂⟩, _⟩ := existsUnique_factor_of_isHomLift hp a d.snd
      (eqToHom hY ≫ p.map c.snd) (by rw [← Category.assoc, ha, hf₂])
    have hcomm : b₁ ≫ f₁ = b₂ ≫ f₂ := by
      obtain ⟨l, hl, hu⟩ := existsUnique_factor_of_isHomLift hp a (d.fst ≫ f₁)
        (eqToHom hY ≫ p.map c.fst ≫ p.map f₁) (by
          rw [← Category.assoc, ha, ← Category.assoc, hf₁, p.map_comp])
      apply (hu _ ?_).trans (hu _ ?_).symm
      · exact ⟨by simp [p.map_comp, hb₁], by rw [← Category.assoc, hab₁]⟩
      · constructor
        · rw [p.map_comp, hb₂, Category.assoc, ← p.map_comp, ← c.condition, p.map_comp]
        · rw [← Category.assoc, hab₂, d.condition]
    obtain ⟨l, hl₁, hl₂⟩ := hex Y b₁ b₂ hcomm hY hb₁ hb₂
    exact ⟨a ≫ l, by rw [Category.assoc, hl₁, hab₁], by rw [Category.assoc, hl₂, hab₂]⟩
  refine ⟨PullbackCone.isLimitAux' c fun d => ?_⟩
  exact ⟨(hlift d).choose, (hlift d).choose_spec.1, (hlift d).choose_spec.2,
    fun {m} hm₁ hm₂ => huniq _ _ (hm₁.trans (hlift d).choose_spec.1.symm)
      (hm₂.trans (hlift d).choose_spec.2.symm)⟩

/-- The pair `(ULift k, V)`: the special-fibre object formed over the residue-field object with
carrier `ULift k`, so that it lies in the fibre of the projection over that object. -/
private noncomputable def residueFiberPoint
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) where
  base := residueFieldObject.{u, w, w} Λ k
  carrier := V
  module := by
    change Module (ULift.{w} k) V
    exact Module.compHom V
      (ULift.algEquiv (R := Λ) (A := k)).toRingEquiv.toRingHom
  finite := by
    let e : ULift.{w} k ≃+* k := (ULift.algEquiv (R := Λ) (A := k)).toRingEquiv
    let : Module (residueFieldObject.{u, w, w} Λ k) V := by
      change Module (ULift.{w} k) V
      exact Module.compHom V e.toRingHom
    have hfg : (⊤ : Submodule k V).FG := Module.Finite.fg_top
    obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
    have hspanLift : Submodule.span (ULift.{w} k) s = ⊤ := by
      refine top_unique fun x _ => ?_
      refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (ULift.{w} k) s)
        (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _)
        (fun _ _ _ _ => Submodule.add_mem _) (fun a y _ py => ?_)
        (hspan.symm ▸ Submodule.mem_top : x ∈ Submodule.span k s)
      obtain ⟨b, rfl⟩ := e.surjective a
      exact Submodule.smul_mem _ b py
    exact Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨s, hs, hspanLift⟩)
  projective := by
    let e : ULift.{w} k ≃+* k := (ULift.algEquiv (R := Λ) (A := k)).toRingEquiv
    let : Module (residueFieldObject.{u, w, w} Λ k) V := by
      change Module (ULift.{w} k) V
      exact Module.compHom V e.toRingHom
    have : Module.Free (residueFieldObject.{u, w, w} Λ k) V := by
      change Module.Free (ULift.{w} k) V
      let : RingHomInvPair (e.symm : k →+* ULift.{w} k)
          (e : ULift.{w} k →+* k) := RingHomInvPair.of_ringEquiv e.symm
      let : RingHomInvPair (e : ULift.{w} k →+* k)
          (e.symm : k →+* ULift.{w} k) := RingHomInvPair.of_ringEquiv e
      let f : V ≃ₛₗ[(e.symm : k →+* ULift.{w} k)] V :=
        { toFun := id
          invFun := id
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl
          map_add' := by intro x y; rfl
          map_smul' := by intro a x; rfl }
      exact Module.Free.of_equiv f
    exact Module.Projective.of_free

/-- The object `(ULift k, V)` lies in the fibre of the projection over the residue-field
object. -/
private lemma residueFiberPoint_mem_fiber
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    letI := 𝓕.category
    (𝓕.projection).obj (residueFiberPoint (Λ := Λ) (k := k) V) =
      residueFieldObject.{u, w, w} Λ k := by
  let := 𝓕.category
  rw [𝓕.projection_obj]
  rfl

/-- The comparison morphism from the special-fibre object `(k, V)` to `(ULift k, V)`. -/
private noncomputable def specialFiber_hom_residueFiberPoint
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    FiniteProjectiveModule.Hom
      (specialFiber (Λ := Λ) (k := k) V) (residueFiberPoint (Λ := Λ) (k := k) V) := by
  classical
  dsimp only [specialFiber, residueFieldBase, residueFieldObject, residueFiberPoint]
  let e : ULift.{w} k ≃ₐ[Λ] k := ULift.algEquiv (R := Λ) (A := k)
  let α : k ≃ₐ[Λ] ULift.{w} k := e.symm
  refine ⟨?_, ?_, ?_⟩
  · refine
      { hom := α.toAlgHom
        isLocal := by infer_instance
        residue_comm := ?_ }
    intro a
    change (residueFieldObject.{u, w, w} Λ k).residueEquiv
        (IsLocalRing.residue (ULift.{w} k) (α a)) =
      (residueFieldBase Λ k).residueEquiv (IsLocalRing.residue k a)
    rw [residueFieldObject_residueEquiv_residue, residueFieldBase_residueEquiv_residue]
    simp [α, e]
  · exact
      { toFun := id
        map_add' := by intro x y; rfl
        map_smul' := by
          intro a x
          change a • x = e (α a) • x
          simp [α, e] }
  · let : Algebra k (ULift.{w} k) := α.toAlgHom.toRingHom.toAlgebra
    let : Module (ULift.{w} k) V := Module.compHom V e.toRingEquiv.toRingHom
    have hTower : IsScalarTower k (ULift.{w} k) V := ⟨by
      intro a b x
      change e (α a * b) • x = a • (e b • x)
      rw [map_mul, e.apply_symm_apply, mul_smul]⟩
    let : IsScalarTower k (ULift.{w} k) V := hTower
    have hsurj : Function.Surjective (algebraMap k (ULift.{w} k)) := by
      change Function.Surjective (α.toRingEquiv : k → ULift.{w} k)
      exact α.toRingEquiv.surjective
    have : Algebra.IsEpi k (ULift.{w} k) :=
      Algebra.isEpi_of_surjective_algebraMap k (ULift.{w} k) hsurj
    change ∃ e' : TensorProduct k (ULift.{w} k) V ≃ₗ[ULift.{w} k] V,
      ∀ m, e' (TensorProduct.tmul k (1 : ULift.{w} k) m) = m
    let l : TensorProduct k (ULift.{w} k) V ≃ₗ[ULift.{w} k] V :=
      @TensorProduct.lid' k (ULift.{w} k) inferInstance inferInstance inferInstance
        inferInstance V inferInstance inferInstance inferInstance hTower
    refine ⟨l, ?_⟩
    intro m
    calc
      l (TensorProduct.tmul k (1 : ULift.{w} k) m) = (1 : ULift.{w} k) • m := by
        change (@TensorProduct.lid' k (ULift.{w} k) inferInstance inferInstance
          inferInstance ‹Algebra.IsEpi k (ULift.{w} k)› V inferInstance inferInstance
          inferInstance hTower) (TensorProduct.tmul k (1 : ULift.{w} k) m) = _
        exact @TensorProduct.lid'_apply_tmul k (ULift.{w} k) inferInstance inferInstance
          inferInstance ‹Algebra.IsEpi k (ULift.{w} k)› V inferInstance inferInstance
          inferInstance hTower (1 : ULift.{w} k) m
      _ = m := one_smul _ _

/-- The comparison morphism from `(k, V)` to `(ULift k, V)` is an isomorphism: it lies over an
isomorphism of base algebras, and the projection is cofibered in groupoids. -/
private noncomputable def specialFiber_residueFiberPoint_iso
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    letI := 𝓕.category
    specialFiber (Λ := Λ) (k := k) V ≅ residueFiberPoint (Λ := Λ) (k := k) V := by
  letI := 𝓕.category
  let x := specialFiber (Λ := Λ) (k := k) V
  let y := residueFiberPoint (Λ := Λ) (k := k) V
  let f : x ⟶ y := (𝓕.homEquiv x y).symm
    (specialFiber_hom_residueFiberPoint (Λ := Λ) (k := k) V)
  have hbase : (𝓕.homEquiv x y f).base = (residueFieldBaseIso (Λ := Λ) (k := k)).hom := by
    apply ArtinianLocalAlgCat.hom_ext
    ext a
    simp [f, specialFiber_hom_residueFiberPoint, residueFieldBaseIso]
    rfl
  have hmap' : 𝓕.projection.map f =
      eqToHom (𝓕.projection_obj x) ≫
        (residueFieldBaseIso (Λ := Λ) (k := k)).hom ≫
          eqToHom (𝓕.projection_obj y).symm := by
    rw [𝓕.projection_map_eq f, hbase]
    rfl
  have hiso : IsIso (𝓕.projection.map f) := by
    rw [hmap']
    exact ((eqToIso (𝓕.projection_obj x)).trans
      ((residueFieldBaseIso (Λ := Λ) (k := k)).trans
        (eqToIso (𝓕.projection_obj y).symm))).isIso_hom
  letI : IsIso (𝓕.projection.map f) := hiso
  letI : IsIso f := isIso_of_isIso_map (Family.projection_isCofiberedInGroupoids 𝓕) f
  exact asIso f

/-- A module over an object of `𝒞_Λ` whose extension of scalars to the base of a finite
projective module is identified with (a shrinking of) that module's carrier is small in the
carrier universe. Either the module is trivial, or the carrier is nontrivial, which forces `k`
and hence the whole base algebra into the carrier universe. -/
private lemma small_patch_carrier
    (x₁ : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
    (P : ArtinianLocalAlgCat.{u, w, w} Λ k) [Algebra P x₁.base]
    (N : Type w) [AddCommGroup N] [Module P N] [Module.Finite P N] [Module.Projective P N]
    (ε : TensorProduct P x₁.base N ≃ₗ[x₁.base] x₁.carrier) :
    Small.{t, w} N := by
  by_cases hN : Subsingleton N
  · exact small_subsingleton N
  · have : Nontrivial x₁.carrier := by
      by_contra hx₁
      let : Subsingleton x₁.carrier := not_nontrivial_iff_subsingleton.mp hx₁
      have hTensor : Subsingleton (TensorProduct P x₁.base N) := ε.toEquiv.subsingleton
      exact hN (subsingleton_of_subsingleton_baseChange
        (R := P) (S := x₁.base) (M := N) hTensor)
    have hsmallk : Small.{t} k := small_residueField_of_nontrivial x₁
    let : Small.{t} k := hsmallk
    let : Small.{t, w} P := ArtinianLocalAlgCat.small P
    exact Module.Finite.small P N

/-- Two parallel morphisms of the category of finite projective modules are equal as soon as
their base morphisms and their semilinear maps are. -/
private lemma eq_of_base_of_linear
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    ∀ {Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)} (g h : Y ⟶ Z),
      (𝓕.homEquiv Y Z g).base = (𝓕.homEquiv Y Z h).base →
      (∀ m, (𝓕.homEquiv Y Z g).linear m = (𝓕.homEquiv Y Z h).linear m) → g = h := by
  let := 𝓕.category
  intro Y Z g h hb hl
  exact (𝓕.homEquiv Y Z).injective (Hom.ext_of_base_eq _ _ hb hl)

/-- Two morphisms out of one object into the two legs of a cospan agree over the cospan as soon
as their base morphisms and their semilinear maps do. -/
private lemma eq_comp_of_base_of_linear
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    ∀ {P x₁ x₂ x : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
      (q₁ : P ⟶ x₁) (q₂ : P ⟶ x₂) (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      (𝓕.homEquiv P x₁ q₁).base ≫ (𝓕.homEquiv x₁ x f₁).base =
          (𝓕.homEquiv P x₂ q₂).base ≫ (𝓕.homEquiv x₂ x f₂).base →
      (∀ m, (𝓕.homEquiv x₁ x f₁).linear ((𝓕.homEquiv P x₁ q₁).linear m) =
          (𝓕.homEquiv x₂ x f₂).linear ((𝓕.homEquiv P x₂ q₂).linear m)) →
      q₁ ≫ f₁ = q₂ ≫ f₂ := by
  let := 𝓕.category
  intro P x₁ x₂ x q₁ q₂ f₁ f₂ hb hl
  refine (𝓕.homEquiv P x).injective (Hom.ext_of_base_eq _ _ ?_ fun m => ?_)
  · rw [𝓕.comp_base, 𝓕.comp_base]; exact hb
  · rw [𝓕.comp_linear, 𝓕.comp_linear]; exact hl m

/-- Two morphisms into one object whose projections differ by the identification of their
sources have base morphisms differing by the same identification. -/
private lemma base_eq_of_projection_map_eq
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    ∀ {Y P X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
      (a : Y ⟶ X) (c : P ⟶ X) (hY : Y.base = P.base),
      𝓕.projection.map a = eqToHom ((𝓕.projection_obj Y).trans (hY.trans
        (𝓕.projection_obj P).symm)) ≫ 𝓕.projection.map c →
      (𝓕.homEquiv Y X a).base = eqToHom hY ≫ (𝓕.homEquiv P X c).base := by
  let := 𝓕.category
  intro Y P X a c hY h
  rw [← 𝓕.projection_map a, ← 𝓕.projection_map c, h]
  simp

/-- A pullback square is unchanged by replacing its apex by an isomorphic object. -/
private lemma isPullback_of_iso_apex {C : Type u₁} [Category.{v₁} C]
    {P P' X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {fst' : P' ⟶ X} {snd' : P' ⟶ Y}
    (ε : P' ≅ P) (hfst : ε.hom ≫ fst = fst') (hsnd : ε.hom ≫ snd = snd') :
    IsPullback fst' snd' f g :=
  h.of_iso' ε (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using hfst) (by simpa using hsnd) (by simp) (by simp)

/-- A pullback square of base algebras realized by the base morphisms of a square of finite
projective modules is a pullback square for the projection. -/
private lemma isPullback_projection_of_base
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    ∀ {Y x₁ x₂ x : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
      (a : Y ⟶ x₁) (b : Y ⟶ x₂) (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
      {p₁ : Y.base ⟶ x₁.base} {p₂ : Y.base ⟶ x₂.base},
      (𝓕.homEquiv Y x₁ a).base = p₁ → (𝓕.homEquiv Y x₂ b).base = p₂ →
      IsPullback p₁ p₂ (𝓕.homEquiv x₁ x f₁).base (𝓕.homEquiv x₂ x f₂).base →
      IsPullback (𝓕.projection.map a) (𝓕.projection.map b)
        (𝓕.projection.map f₁) (𝓕.projection.map f₂) := by
  let := 𝓕.category
  intro Y x₁ x₂ x a b f₁ f₂ p₁ p₂ ha hb h
  apply h.of_iso' (eqToIso (𝓕.projection_obj Y)) (eqToIso (𝓕.projection_obj x₁))
    (eqToIso (𝓕.projection_obj x₂)) (eqToIso (𝓕.projection_obj x))
  · rw [← ha, 𝓕.projection_map_eq a]; simp
  · rw [← hb, 𝓕.projection_map_eq b]; simp
  · rw [𝓕.projection_map_eq f₁]; simp
  · rw [𝓕.projection_map_eq f₂]; simp

section FibreProduct

variable {A₁ A₂ A : ArtinianLocalAlgCat.{u, w, w} Λ k}
  (g₁ : A₁ ⟶ A) (g₂ : A₂ ⟶ A) (hs : Function.Surjective g₂.hom)
  (s : RingFibreProduct.Situation g₁.hom.toRingHom g₂.hom.toRingHom
    (RingHom.ker g₂.hom.toRingHom))

include hs

/-- The `Λ`-algebra structure on the ring fibre product of the underlying ring maps of a
cospan of `𝒞_Λ`, transported from the algebra fibre product that
`Deformation.ArtinianLocalAlgCat.pullbackObj_of_surjective` provides. -/
private noncomputable abbrev fibreProductAlgebra : Algebra Λ s.fibreProduct :=
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).algebra
  letI : CommRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  (((ringPullbackEquivAlgPullback g₁.hom g₂.hom).symm.toRingHom).comp
      (algebraMap Λ
        (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)))).toAlgebra

/-- The ring fibre product is Artinian. -/
private theorem isArtinianRing_fibreProduct : IsArtinianRing s.fibreProduct :=
  let := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  let : CommRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  let : IsArtinianRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).isArtinianRing
  RingEquiv.isArtinianRing (ringPullbackEquivAlgPullback g₁.hom g₂.hom).symm

/-- The ring fibre product is local. -/
@[ega "IV 19.3.2.1" "(ii): G is a local ring"]
private theorem isLocalRing_fibreProduct : IsLocalRing s.fibreProduct :=
  let := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  let : CommRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  let : IsLocalRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).isLocalRing
  RingEquiv.isLocalRing (ringPullbackEquivAlgPullback g₁.hom g₂.hom).symm

/-- The comparison of the ring fibre product with the algebra fibre product, as a `Λ`-algebra
equivalence. -/
private noncomputable def fibreProductAlgEquiv :
    letI := fibreProductAlgebra g₁ g₂ hs s
    s.fibreProduct ≃ₐ[Λ]
      ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs) := by
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).algebra
  letI : CommRing (AlgHom.pullback g₁.hom g₂.hom) :=
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  letI := fibreProductAlgebra g₁ g₂ hs s
  refine AlgEquiv.ofRingEquiv (f := ringPullbackEquivAlgPullback g₁.hom g₂.hom) ?_
  intro a
  change (ringPullbackEquivAlgPullback g₁.hom g₂.hom)
    (((ringPullbackEquivAlgPullback g₁.hom g₂.hom).symm.toRingHom.comp
      (algebraMap Λ
        (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)))) a) = _
  exact (ringPullbackEquivAlgPullback g₁.hom g₂.hom).apply_symm_apply _

/-- The residue-field identification of the ring fibre product, transported along the
comparison with the algebra fibre product. -/
private noncomputable def fibreProductResidueEquiv :
    letI := fibreProductAlgebra g₁ g₂ hs s
    letI := isLocalRing_fibreProduct g₁ g₂ hs s
    IsLocalRing.ResidueField s.fibreProduct ≃ₐ[Λ] k := by
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).algebra
  letI := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).isLocalRing
  letI := fibreProductAlgebra g₁ g₂ hs s
  letI := isLocalRing_fibreProduct g₁ g₂ hs s
  letI : IsLocalHom (fibreProductAlgEquiv g₁ g₂ hs s).toRingEquiv.toRingHom :=
    ⟨fun a ha =>
      (MulEquiv.isUnit_map (fibreProductAlgEquiv g₁ g₂ hs s).toRingEquiv).mp ha⟩
  exact (IsLocalRing.ResidueField.mapAlgEquiv (fibreProductAlgEquiv g₁ g₂ hs s)).trans
    (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).residueEquiv

/-- The residue-field identification of the ring fibre product, on representatives. -/
private theorem fibreProductResidueEquiv_residue :
    letI := fibreProductAlgebra g₁ g₂ hs s
    letI := isLocalRing_fibreProduct g₁ g₂ hs s
    ∀ a : s.fibreProduct,
      fibreProductResidueEquiv g₁ g₂ hs s (IsLocalRing.residue s.fibreProduct a) =
        (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).residueEquiv
          (IsLocalRing.residue
            (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs))
            (fibreProductAlgEquiv g₁ g₂ hs s a)) := by
  let := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).commRing
  let := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).algebra
  let := (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).isLocalRing
  let := fibreProductAlgebra g₁ g₂ hs s
  let := isLocalRing_fibreProduct g₁ g₂ hs s
  let : IsLocalHom (fibreProductAlgEquiv g₁ g₂ hs s).toRingEquiv.toRingHom :=
    ⟨fun a ha =>
      (MulEquiv.isUnit_map (fibreProductAlgEquiv g₁ g₂ hs s).toRingEquiv).mp ha⟩
  intro a
  change (ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ (Or.inr hs)).residueEquiv
      ((IsLocalRing.ResidueField.mapAlgEquiv (fibreProductAlgEquiv g₁ g₂ hs s))
        (IsLocalRing.residue s.fibreProduct a)) = _
  rw [IsLocalRing.ResidueField.mapAlgEquiv_residue]

/-- The underlying ring map of the first projection of the algebra fibre product, precomposed
with the comparison, is the first projection of the ring fibre product. -/
private theorem fibreProductFst_toRingHom :
    letI := fibreProductAlgebra g₁ g₂ hs s
    s.pullbackCone.fst.hom =
      ((ArtinianLocalAlgCat.pullbackFst_of_surjective g₁ g₂ (Or.inr hs)).hom.comp
        (fibreProductAlgEquiv g₁ g₂ hs s).toAlgHom).toRingHom := by
  let := fibreProductAlgebra g₁ g₂ hs s
  have hp := ArtinianLocalAlgCat.pullbackFst_of_surjective_hom g₁ g₂ (Or.inr hs)
  ext a
  change s.pullbackCone.fst.hom a =
    (ArtinianLocalAlgCat.pullbackFst_of_surjective g₁ g₂ (Or.inr hs)).hom
      (fibreProductAlgEquiv g₁ g₂ hs s a)
  rw [hp]
  rfl

/-- The same for the second projection. -/
private theorem fibreProductSnd_toRingHom :
    letI := fibreProductAlgebra g₁ g₂ hs s
    s.pullbackCone.snd.hom =
      ((ArtinianLocalAlgCat.pullbackSnd_of_surjective g₁ g₂ (Or.inr hs)).hom.comp
        (fibreProductAlgEquiv g₁ g₂ hs s).toAlgHom).toRingHom := by
  let := fibreProductAlgebra g₁ g₂ hs s
  have hp := ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom g₁ g₂ (Or.inr hs)
  ext a
  change s.pullbackCone.snd.hom a =
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective g₁ g₂ (Or.inr hs)).hom
      (fibreProductAlgEquiv g₁ g₂ hs s a)
  rw [hp]
  rfl

end FibreProduct

/-- Finite projective modules over Artinian local algebras satisfy the Rim–Schlessinger
condition: a cospan whose second base morphism is surjective is covered by the Milnor patch of
the two modules over the fibre product of the base algebras. -/
@[stacks 0DVP "Rim-Schlessinger condition"]
public theorem Family.satisfiesRS_projection
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    SatisfiesRS 𝓕.projection := by
  refine ⟨Family.projection_isCofiberedInGroupoids 𝓕, ?_⟩
  intro x₁ x₂ x f₁ f₂ hsurj
  let : Category.{max w t}
      (FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) := 𝓕.category
  let h₁ := 𝓕.homEquiv x₁ x f₁
  let h₂ := 𝓕.homEquiv x₂ x f₂
  have hsurj₂ := Family.homEquiv_base_surjective 𝓕 f₂ hsurj
  let pb := ArtinianLocalAlgCat.pullbackObj_of_surjective
    h₁.base h₂.base (Or.inr hsurj₂)
  let pb₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective
    h₁.base h₂.base (Or.inr hsurj₂)
  let pb₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    h₁.base h₂.base (Or.inr hsurj₂)
  let : Algebra x₁.base x.base := h₁.base.hom.toRingHom.toAlgebra
  let : Algebra x₂.base x.base := h₂.base.hom.toRingHom.toAlgebra
  obtain ⟨e₁, he₁⟩ := h₁.baseChange
  obtain ⟨e₂, he₂⟩ := h₂.baseChange
  let : Small.{w, t} x₁.carrier := small_carrier x₁
  let : Small.{w, t} x₂.carrier := small_carrier x₂
  let s : RingFibreProduct.Situation h₁.base.hom.toRingHom h₂.base.hom.toRingHom
      (RingHom.ker h₂.base.hom.toRingHom) := ⟨hsurj₂, rfl⟩
  let := fibreProductAlgebra h₁.base h₂.base hsurj₂ s
  let := isArtinianRing_fibreProduct h₁.base h₂.base hsurj₂ s
  let := isLocalRing_fibreProduct h₁.base h₂.base hsurj₂ s
  let rhoAlg := fibreProductAlgEquiv h₁.base h₂.base hsurj₂ s
  let : IsLocalHom rhoAlg.toRingEquiv.toRingHom :=
    ⟨fun a ha => (MulEquiv.isUnit_map rhoAlg.toRingEquiv).mp ha⟩
  let pbPatch : ArtinianLocalAlgCat.{u, w, w} Λ k :=
    ⟨s.fibreProduct, fibreProductResidueEquiv h₁.base h₂.base hsurj₂ s⟩
  let rhoHom : pbPatch ⟶ pb :=
    { hom := rhoAlg.toAlgHom
      isLocal := ⟨fun a ha => (MulEquiv.isUnit_map rhoAlg.toRingEquiv).mp ha⟩
      residue_comm := fun a =>
        fibreProductResidueEquiv_residue h₁.base h₂.base hsurj₂ s a }
  have : IsIso rhoHom :=
    ArtinianLocalAlgCat.isIso_of_bijective_hom rhoHom rhoAlg.bijective
  let pbFst : pbPatch ⟶ x₁.base := rhoHom ≫ pb₁
  let pbSnd : pbPatch ⟶ x₂.base := rhoHom ≫ pb₂
  have hpbFst : s.pullbackCone.fst.hom = pbFst.hom.toRingHom :=
    fibreProductFst_toRingHom h₁.base h₂.base hsurj₂ s
  have hpbSnd : s.pullbackCone.snd.hom = pbSnd.hom.toRingHom :=
    fibreProductSnd_toRingHom h₁.base h₂.base hsurj₂ s
  let rhoIso : pbPatch ≅ pb := asIso rhoHom
  have hbase : IsPullback pbFst pbSnd h₁.base h₂.base :=
    isPullback_of_iso_apex
      (ArtinianLocalAlgCat.isPullback_of_surjective h₁.base h₂.base (Or.inr hsurj₂))
      rhoIso (by ext a; rfl) (by ext a; rfl)
  let : Algebra s.fibreProduct x₁.base := s.pullbackCone.fst.hom.toAlgebra
  let : Algebra s.fibreProduct x₂.base := s.pullbackCone.snd.hom.toAlgebra
  obtain ⟨N, hNfin, hNproj, ε₁, ε₂, hεcompat, hεinj, hεuniv⟩ :=
    exists_patch_universal h₁.base.hom.toRingHom h₂.base.hom.toRingHom hsurj₂
      x₁.carrier x₂.carrier (e₁.trans e₂.symm)
  let : Module.Finite s.fibreProduct N := hNfin
  let : Module.Projective s.fibreProduct N := hNproj
  have hsmallN : Small.{t, w} N := small_patch_carrier x₁ pbPatch N ε₁
  let : Small.{t, w} N := hsmallN
  let N' := Shrink.{t, w} N
  let en : N' ≃ₗ[s.fibreProduct] N := Shrink.linearEquiv s.fibreProduct N
  let : Module.Finite s.fibreProduct N' := Module.Finite.equiv en.symm
  let : Module.Projective s.fibreProduct N' := Module.Projective.of_equiv' en.symm
  let patchObject : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) :=
    ⟨pbPatch, N'⟩
  let e₁' : TensorProduct s.fibreProduct x₁.base N' ≃ₗ[x₁.base] x₁.carrier :=
    (LinearEquiv.baseChange s.fibreProduct x₁.base N' N en).trans ε₁
  let e₂' : TensorProduct s.fibreProduct x₂.base N' ≃ₗ[x₂.base] x₂.carrier :=
    (LinearEquiv.baseChange s.fibreProduct x₂.base N' N en).trans ε₂
  let patchHom₁ := homOfBaseChange' (X := patchObject) (Y := x₁) pbFst
    s.pullbackCone.fst.hom hpbFst e₁'
  let patchHom₂ := homOfBaseChange' (X := patchObject) (Y := x₂) pbSnd
    s.pullbackCone.snd.hom hpbSnd e₂'
  let patchArrow₁ : patchObject ⟶ x₁ := (𝓕.homEquiv patchObject x₁).symm patchHom₁
  let patchArrow₂ : patchObject ⟶ x₂ := (𝓕.homEquiv patchObject x₂).symm patchHom₂
  have har₁ : 𝓕.homEquiv patchObject x₁ patchArrow₁ = patchHom₁ :=
    (𝓕.homEquiv patchObject x₁).apply_symm_apply _
  have har₂ : 𝓕.homEquiv patchObject x₂ patchArrow₂ = patchHom₂ :=
    (𝓕.homEquiv patchObject x₂).apply_symm_apply _
  have hph₁ (m : N') : patchHom₁.linear m =
      ε₁ (TensorProduct.tmul s.fibreProduct (1 : x₁.base) (en m)) :=
    homOfBaseChange'_linear (X := patchObject) (Y := x₁) pbFst
      s.pullbackCone.fst.hom hpbFst e₁' m
  have hph₂ (m : N') : patchHom₂.linear m =
      ε₂ (TensorProduct.tmul s.fibreProduct (1 : x₂.base) (en m)) :=
    homOfBaseChange'_linear (X := patchObject) (Y := x₂) pbSnd
      s.pullbackCone.snd.hom hpbSnd e₂' m
  have hpb₁ : patchHom₁.base = pbFst :=
    homOfBaseChange'_base (X := patchObject) (Y := x₁) pbFst
      s.pullbackCone.fst.hom hpbFst e₁'
  have hpb₂ : patchHom₂.base = pbSnd :=
    homOfBaseChange'_base (X := patchObject) (Y := x₂) pbSnd
      s.pullbackCone.snd.hom hpbSnd e₂'
  have patchArrow_condition : patchArrow₁ ≫ f₁ = patchArrow₂ ≫ f₂ :=
    eq_comp_of_base_of_linear 𝓕 patchArrow₁ patchArrow₂ f₁ f₂
      (by rw [har₁, har₂, hpb₁, hpb₂]; exact hbase.w)
      (by
        intro m
        rw [har₁, har₂, hph₁, hph₂, ← he₁, ← he₂]
        exact e₂.symm.injective ((hεcompat (en m)).trans (e₂.symm_apply_apply _).symm))
  have hpc : IsPullback (𝓕.projection.map patchArrow₁) (𝓕.projection.map patchArrow₂)
      (𝓕.projection.map f₁) (𝓕.projection.map f₂) :=
    isPullback_projection_of_base 𝓕 patchArrow₁ patchArrow₂ f₁ f₂
      (by rw [har₁]; exact hpb₁) (by rw [har₂]; exact hpb₂) hbase
  let c := PullbackCone.mk patchArrow₁ patchArrow₂ patchArrow_condition
  have hcl : IsLimit (c.map 𝓕.projection) := hpc.isLimit
  refine ⟨c, ?_, ⟨hcl⟩⟩
  apply cofibered_pullback_isLimit 𝓕.projection
    (Family.projection_isCofiberedInGroupoids 𝓕) c hcl
  · dsimp only [c, PullbackCone.mk]
    intro Y a b hab hY ha hb
    have hYbase : Y.base = pbPatch :=
      (𝓕.projection_obj Y).symm.trans (hY.trans (𝓕.projection_obj patchObject))
    rcases Y with ⟨Ybase, M, hAdd, hMod, hFin, hProj⟩
    dsimp only at hYbase
    subst Ybase
    let Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) := ⟨pbPatch, M⟩
    let ga := 𝓕.homEquiv Y x₁ a
    let gb := 𝓕.homEquiv Y x₂ b
    have hga : ga.base = pbFst := by
      simpa [har₁, hpb₁] using base_eq_of_projection_map_eq 𝓕 a patchArrow₁ rfl ha
    have hgb : gb.base = pbSnd := by
      simpa [har₂, hpb₂] using base_eq_of_projection_map_eq 𝓕 b patchArrow₂ rfl hb
    obtain ⟨ay, hay⟩ := baseChange_of_ringHom_eq ga s.pullbackCone.fst.hom
      ((congrArg (fun f => f.hom.toRingHom) hga).trans hpbFst.symm)
    obtain ⟨by', hby⟩ := baseChange_of_ringHom_eq gb s.pullbackCone.snd.hom
      ((congrArg (fun f => f.hom.toRingHom) hgb).trans hpbSnd.symm)
    let : Small.{w, t} M := small_carrier Y
    let : Module.Flat s.fibreProduct M := Module.Flat.of_projective
    obtain ⟨l, hl⟩ := hεuniv M ay by' (by
      intro m
      change e₂.symm (e₁ (TensorProduct.tmul x₁.base (1 : x.base)
          (ay (TensorProduct.tmul s.fibreProduct (1 : x₁.base) m)))) =
        TensorProduct.tmul x₂.base (1 : x.base)
          (by' (TensorProduct.tmul s.fibreProduct (1 : x₂.base) m))
      rw [LinearEquiv.symm_apply_eq, hay, hby, he₁, he₂]
      have hh := congrArg (fun f => (𝓕.homEquiv Y x f).linear m) hab
      rw [𝓕.comp_linear, 𝓕.comp_linear] at hh
      exact hh)
    let l' : M ≃ₗ[s.fibreProduct] N' := l.trans en.symm
    let lh : FiniteProjectiveModule.Hom Y patchObject :=
      { base := 𝟙 pbPatch
        linear := l'.toLinearMap
        baseChange := ⟨(TensorProduct.lid s.fibreProduct M).trans l',
          fun m => congrArg l' (one_smul s.fibreProduct m)⟩ }
    let lift : Y ⟶ patchObject := (𝓕.homEquiv Y patchObject).symm lh
    have hlift : 𝓕.homEquiv Y patchObject lift = lh :=
      (𝓕.homEquiv Y patchObject).apply_symm_apply _
    have hen' (m : M) : en (l' m) = l m := en.apply_symm_apply (l m)
    refine ⟨lift, ?_, ?_⟩
    · refine eq_of_base_of_linear 𝓕 (lift ≫ patchArrow₁) a ?_ ?_
      · rw [𝓕.comp_base, hlift, har₁, hpb₁]
        exact (Category.id_comp pbFst).trans hga.symm
      · intro m
        rw [𝓕.comp_linear, hlift, har₁]
        exact ((hph₁ (l' m)).trans (congrArg
          (fun z => ε₁ (TensorProduct.tmul s.fibreProduct (1 : x₁.base) z))
          (hen' m))).trans (((hl m).1).trans (hay m))
    · refine eq_of_base_of_linear 𝓕 (lift ≫ patchArrow₂) b ?_ ?_
      · rw [𝓕.comp_base, hlift, har₂, hpb₂]
        exact (Category.id_comp pbSnd).trans hgb.symm
      · intro m
        rw [𝓕.comp_linear, hlift, har₂]
        exact ((hph₂ (l' m)).trans (congrArg
          (fun z => ε₂ (TensorProduct.tmul s.fibreProduct (1 : x₂.base) z))
          (hen' m))).trans (((hl m).2).trans (hby m))
  · dsimp only [c, PullbackCone.mk]
    intro Y a b ha hb
    refine eq_of_base_of_linear 𝓕 a b ?_ ?_
    · have heq : 𝓕.projection.map a = 𝓕.projection.map b := by
        apply hpc.hom_ext
        · simpa only [← Functor.map_comp] using congrArg 𝓕.projection.map ha
        · simpa only [← Functor.map_comp] using congrArg 𝓕.projection.map hb
      rw [← 𝓕.projection_map a, ← 𝓕.projection_map b, heq]
    · intro m
      apply en.injective
      apply hεinj
      refine Prod.ext ?_ ?_
      · have hh := congrArg (fun f => (𝓕.homEquiv Y x₁ f).linear m) ha
        rw [𝓕.comp_linear, 𝓕.comp_linear, har₁] at hh
        exact ((hph₁ _).symm.trans hh).trans (hph₁ _)
      · have hh := congrArg (fun f => (𝓕.homEquiv Y x₂ f).linear m) hb
        rw [𝓕.comp_linear, 𝓕.comp_linear, har₂] at hh
        exact ((hph₂ _).symm.trans hh).trans (hph₂ _)

/-- Deformations of a finite-dimensional vector space form a deformation category. -/
@[stacks 0DVP "deformation category"]
public theorem isDeformationCategory_deformationCategory
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    let 𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k) :=
      FiniteProjectiveModule.family (Λ := Λ) (k := k)
    letI := 𝓕.category
    IsDeformationCategory
      (objectsOverFunctor 𝓕.projection
        (FiniteProjectiveModule.specialFiber (Λ := Λ) (k := k) V)) := by
  let 𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k) :=
    FiniteProjectiveModule.family (Λ := Λ) (k := k)
  let := 𝓕.category
  let y := residueFiberPoint (Λ := Λ) (k := k) V
  have hd := isDeformationCategory_objectsOverFunctor 𝓕.projection
    (Family.satisfiesRS_projection 𝓕) ⟨y, residueFiberPoint_mem_fiber 𝓕 V⟩
  let ecomp := specialFiber_residueFiberPoint_iso 𝓕 V
  exact isDeformationCategory_comp (Over.map ecomp.hom) (over_map_obj_surjective ecomp)
    (objectsOverFunctor 𝓕.projection y) hd

end Deformation.Examples.FiniteProjectiveModule
