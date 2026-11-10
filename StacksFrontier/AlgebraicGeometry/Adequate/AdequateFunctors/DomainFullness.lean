module

public import StacksFrontier.Algebra.Module.Adequate.Defs

/-!
# Extension of scalars is full on a restricted domain of algebras

Extension of scalars `M ↦ (B ↦ B ⊗[A] M)` from `A`-modules to module-valued functors on *all*
commutative `A`-algebras is fully faithful, which is
`AdequateFunctor.fullyFaithfulModuleExtensionFunctor`. That full faithfulness is what the library's
proofs of [Stacks, Tags 06V2 and 06V3] use to recover a map of modules from a map of module
extensions; on a restricted domain `ι : C ⥤ CommAlgCat A` no such statement is available, and
the two tags are therefore proved only for the full domain of algebras.

This file supplies it. A morphism of module extensions is determined by its value at the base
ring, by naturality and semilinearity; so all that the restricted domain must provide is the
base ring, as an object mapping to every object of the domain. That data is
`AdequateFunctor.BaseAlgebraObject`, and the domain that matters geometrically has it: the base
ring is an algebra of the site exactly when its spectrum is an object of the site, which is the
standing hypothesis of the site-domain closure properties.

## Main definitions

* `AdequateFunctor.BaseAlgebraObject` — the base ring as a weakly initial object of a domain of
  algebras: an object of the domain whose algebra is the base ring, together with a morphism
  from it to every object.
* `AdequateFunctor.BaseAlgebraObject.siteOfSpecMem` — the base ring is such an object of the
  site algebras as soon as its spectrum belongs to the site.
* `AdequateFunctor.moduleHomOfExtensionNatTransOn` — the map of modules underlying a morphism of
  module extensions on a domain of algebras, read off at the base ring.
* `AdequateFunctor.fullyFaithfulModuleExtensionFunctorOn` — extension of scalars to the
  module-valued functors on a domain of algebras with a base object is fully faithful.

## Main results

* `AdequateFunctor.moduleExtension_natTransOn_eq_map` — every morphism between module extensions
  on a domain of algebras with a base object is the base change of a map of modules.

## Implementation notes

`BaseAlgebraObject` records its algebra as *isomorphic to* the lifted base ring rather than
equal to it. That is what makes the geometric instance free of any cardinality argument: the
object of the site is `A` itself, whose spectrum is assumed to be in the site, and the
comparison with `ULift A` is the canonical algebra equivalence. Demanding equality instead
would require knowing that `Spec (ULift A)` is in the site, i.e. that the size bound defining
the site is invariant under isomorphism of schemes, which is a fact about the cutoff rather than
about algebra.

The proof mirrors `AdequateFunctor.moduleExtension_natTrans_eq_map`, with the unique algebra map
out of the base ring replaced by the structural morphism out of the base object: a pure tensor
`b ⊗ m` is `b • (1 ⊗ m)`, the element `1 ⊗ m` is the image of `(1 : A) ⊗ m` under the structural
morphism, and naturality together with semilinearity then pins the value down.

## References

* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

universe w v u u₁ v₁

namespace AdequateFunctor

/-- An algebra map out of an algebra isomorphic to the base ring sends an element to the scalar
image of its preimage in the base ring. -/
private theorem algHom_apply_of_algEquiv {A : Type u} [CommRing A] {T Y : CommAlgCat.{max u v} A}
    (e : (T : Type (max u v)) ≃ₐ[A] ULift.{v} A) (f : T ⟶ Y) (t : (T : Type (max u v))) :
    f.hom t = algebraMap A (Y : Type (max u v)) (e t).down := by
  have h : t = algebraMap A (T : Type (max u v)) (e t).down := by
    calc t = e.symm (e t) := (e.symm_apply_apply t).symm
      _ = e.symm (algebraMap A (ULift.{v} A) (e t).down) := rfl
      _ = algebraMap A (T : Type (max u v)) (e t).down := e.symm.toAlgHom.commutes _
  conv_lhs => rw [h]
  exact f.hom.commutes _

/-! ### The base ring as an object of a domain of algebras -/

/-- The base ring as a weakly initial object of a domain of algebras `ι`: an object of the
domain whose algebra is the base ring, together with a morphism from it to every object of the
domain. This is the only thing a domain of algebras must provide for extension of scalars to it
to be full. -/
public structure BaseAlgebraObject {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A) where
  /-- the object of the domain carrying the base ring -/
  base : C
  /-- its algebra is the base ring -/
  equiv : (ι.obj base : Type (max u v)) ≃ₐ[A] ULift.{v} A
  /-- it maps to every object of the domain -/
  hom (X : C) : base ⟶ X

namespace BaseAlgebraObject

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
  {ι : C ⥤ CommAlgCat.{max u v} A} (b : BaseAlgebraObject.{v} ι)

/-- The object of the domain of algebras at which a morphism of module extensions is
evaluated. -/
public abbrev obj : ((Cᵒᵖ)ᵒᵖ) := op (op b.base)

/-- The base object's algebra is the base ring: an element is the image of its unique
preimage in the base ring. -/
public lemma equiv_symm_one : b.equiv.symm (1 : ULift.{v} A) = 1 := map_one _

/-- An element of the base object's algebra is the structural image of a scalar. -/
public lemma eq_algebraMap (t : (ι.obj b.base : Type (max u v))) :
    t = algebraMap A (ι.obj b.base : Type (max u v)) (b.equiv t).down :=
  algHom_apply_of_algEquiv b.equiv (𝟙 _) t

/-- Any morphism out of the base object is the structure map on the nose: its value at an
element is the scalar image of that element's preimage in the base ring. -/
public lemma hom_apply {X : C} (t : (ι.obj b.base : Type (max u v))) :
    (ι.map (b.hom X)).hom t = algebraMap A (ι.obj X : Type (max u v)) (b.equiv t).down :=
  algHom_apply_of_algEquiv b.equiv _ t

end BaseAlgebraObject

/-! ### Reading off the underlying map of modules -/

section Full

variable {A : Type u} [CommRing A]

/-! #### The computation at an algebra isomorphic to the base ring

These two lemmas are stated for the module extension on *all* algebras, where the sections over
an algebra are reducibly the tensor product. The restricted-domain statements are these ones
reindexed, which is a definitional change of the morphism being restricted along. -/

/-- Evaluating a module extension at an algebra isomorphic to the base ring recovers the
module. -/
public noncomputable def moduleExtensionAtBaseEquivOfAlgEquiv {T : CommAlgCat.{max u v} A}
    (e : (T : Type (max u v)) ≃ₐ[A] ULift.{v} A) (M : ModuleCat.{w} A) :
    (T : Type (max u v)) ⊗[A] M ≃ₗ[A] M :=
  (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)).trans
    (moduleExtensionAtBaseEquiv.{w, v} M)

public lemma moduleExtensionAtBaseEquivOfAlgEquiv_symm_apply {T : CommAlgCat.{max u v} A}
    (e : (T : Type (max u v)) ≃ₐ[A] ULift.{v} A) (M : ModuleCat.{w} A) (m : M) :
    (moduleExtensionAtBaseEquivOfAlgEquiv.{w} e M).symm m = (1 : (T : Type (max u v))) ⊗ₜ[A] m := by
  change (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)).symm
      ((1 : ULift.{v} A) ⊗ₜ[A] m) = _
  rw [TensorProduct.congr_symm_tmul,
    show e.toLinearEquiv.symm (1 : ULift.{v} A) = 1 from map_one e.symm]
  rfl

public lemma moduleExtensionAtBaseEquivOfAlgEquiv_tmul {T : CommAlgCat.{max u v} A}
    (e : (T : Type (max u v)) ≃ₐ[A] ULift.{v} A) (M : ModuleCat.{w} A)
    (t : (T : Type (max u v))) (m : M) :
    moduleExtensionAtBaseEquivOfAlgEquiv.{w} e M (t ⊗ₜ[A] m) = (e t).down • m := rfl

/-- Restriction along any algebra map out of an algebra isomorphic to the base ring sends a
section to the pure tensor of the module element it determines. -/
public lemma moduleExtension_map_eq_one_tmul {T Y : CommAlgCat.{max u v} A}
    (e : (T : Type (max u v)) ≃ₐ[A] ULift.{v} A) (u : T ⟶ Y) (N : ModuleCat.{w} A)
    (z : (T : Type (max u v)) ⊗[A] N) :
    (moduleExtension.{w, v} A N).map (u.op.op) z =
      (1 : (Y : Type (max u v))) ⊗ₜ[A] moduleExtensionAtBaseEquivOfAlgEquiv.{w} e N z := by
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
      change u.hom t ⊗ₜ[A] n = (1 : (Y : Type (max u v))) ⊗ₜ[A] ((e t).down • n)
      rw [algHom_apply_of_algEquiv e u t, ← TensorProduct.smul_tmul]
      simp [Algebra.smul_def]
  | add z t hz ht =>
      simp only [map_add, hz, ht, TensorProduct.tmul_add]
      rfl

/-! #### Fullness on a domain of algebras with a base object -/

variable {C : Type u₁} [Category.{v₁} C]
  {ι : C ⥤ CommAlgCat.{max u v} A} (b : BaseAlgebraObject.{v} ι)

/-- Evaluating a module extension at the base object of a domain of algebras recovers the
module. -/
public noncomputable abbrev moduleExtensionAtBaseOnEquiv (M : ModuleCat.{w} A) :
    (ι.obj b.base : Type (max u v)) ⊗[A] M ≃ₗ[A] M :=
  moduleExtensionAtBaseEquivOfAlgEquiv.{w} b.equiv M

/-- Recover the underlying map of modules of a morphism of module extensions on a domain of
algebras, by evaluating at the base object. -/
public noncomputable def moduleHomOfExtensionNatTransOn {M N : ModuleCat.{w} A}
    (η : (moduleExtensionFunctorOn.{w} ι).obj M ⟶ (moduleExtensionFunctorOn.{w} ι).obj N) :
    M ⟶ N := by
  let t : (ι.obj b.base : Type (max u v)) ⊗[A] M →ₗ[(ι.obj b.base : Type (max u v))]
      (ι.obj b.base : Type (max u v)) ⊗[A] N := (η.app b.obj).hom
  exact ModuleCat.ofHom ((moduleExtensionAtBaseOnEquiv.{w} b N).toLinearMap.comp
    ((t.restrictScalars A).comp (moduleExtensionAtBaseOnEquiv.{w} b M).symm.toLinearMap))

/-- Every morphism between module extensions on a domain of algebras with a base object is the
base change of a map of modules: a pure tensor `c ⊗ m` is `c • (1 ⊗ m)`, the section `1 ⊗ m` is
restricted from the base object, and naturality together with semilinearity pins the value
down. -/
public lemma moduleExtension_natTransOn_eq_map {M N : ModuleCat.{w} A}
    (η : (moduleExtensionFunctorOn.{w} ι).obj M ⟶ (moduleExtensionFunctorOn.{w} ι).obj N) :
    η = (moduleExtensionFunctorOn.{w} ι).map (moduleHomOfExtensionNatTransOn.{w} b η) := by
  ext X x
  set Y := X.unop.unop
  set g : b.base ⟶ Y := b.hom Y
  set κ := moduleHomOfExtensionNatTransOn.{w} b η
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    -- the section `1 ⊗ m` over `Y` is restricted from the base object
    have hg₁ : ((moduleExtensionFunctorOn.{w} ι).obj M).map (g.op.op)
        ((moduleExtensionAtBaseOnEquiv.{w} b M).symm m) =
          (1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m := by
      rw [moduleExtensionAtBaseEquivOfAlgEquiv_symm_apply]
      change (ι.map g).hom 1 ⊗ₜ[A] m = _
      rw [map_one]
    -- restricting the image of that section to `Y` is the pure tensor of `κ m`
    have hbase : ((moduleExtensionFunctorOn.{w} ι).obj N).map (g.op.op)
        ((η.app b.obj) ((moduleExtensionAtBaseOnEquiv.{w} b M).symm m)) =
          (1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] κ.hom m :=
      moduleExtension_map_eq_one_tmul.{w} b.equiv (ι.map g) N _
    have hn : (η.app X).hom
        ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m) =
          (1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] κ.hom m := by
      have h := PresheafOfModules.naturality_apply η (g.op.op)
        ((moduleExtensionAtBaseOnEquiv.{w} b M).symm m)
      rwa [hg₁, hbase] at h
    have hc : c • ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m) =
        c ⊗ₜ[A] m := by
      rw [TensorProduct.smul_tmul']
      simp
    have hc' : c • ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] κ.hom m) =
        c ⊗ₜ[A] κ.hom m := by
      rw [TensorProduct.smul_tmul']
      simp
    -- the pattern `η (c • x)` is ill-typed at `implicit` transparency, so this runs in term mode
    have e1 : (η.app X).hom (c ⊗ₜ[A] m) =
        (η.app X).hom (c • ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m)) :=
      congrArg (fun z => (η.app X).hom z) hc.symm
    have e2 : (η.app X).hom (c • ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m)) =
        c • (η.app X).hom ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m) :=
      (η.app X).hom.map_smul c _
    have e3 : c • (η.app X).hom ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] m) =
        c • ((1 : ((ι.op.op.obj X).unop.unop : Type (max u v))) ⊗ₜ[A] κ.hom m) :=
      congrArg (fun z => c • z) hn
    exact e1.trans (e2.trans (e3.trans hc'))
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Recovering the map of modules inverts extension of scalars on morphisms. -/
public lemma moduleHomOfExtensionNatTransOn_map {M N : ModuleCat.{w} A} (f : M ⟶ N) :
    moduleHomOfExtensionNatTransOn.{w} b ((moduleExtensionFunctorOn.{w} ι).map f) = f := by
  ext m
  change moduleExtensionAtBaseOnEquiv.{w} b N
      (((moduleExtensionFunctorOn.{w} ι).map f).app b.obj
        ((moduleExtensionAtBaseOnEquiv.{w} b M).symm m)) = f.hom m
  rw [moduleExtensionAtBaseEquivOfAlgEquiv_symm_apply,
    show (((moduleExtensionFunctorOn.{w} ι).map f).app b.obj
      ((1 : (ι.obj b.base : Type (max u v))) ⊗ₜ[A] m)) =
      (1 : (ι.obj b.base : Type (max u v))) ⊗ₜ[A] f.hom m from rfl,
    moduleExtensionAtBaseEquivOfAlgEquiv_tmul,
    show b.equiv (1 : (ι.obj b.base : Type (max u v))) = 1 from map_one _]
  exact one_smul A _

include b in
/-- Extension of scalars to the module-valued functors on a domain of algebras with a base
object is fully faithful. -/
public noncomputable def fullyFaithfulModuleExtensionFunctorOn :
    (moduleExtensionFunctorOn.{w} ι).FullyFaithful where
  preimage := moduleHomOfExtensionNatTransOn.{w} b
  map_preimage η := (moduleExtension_natTransOn_eq_map.{w} b η).symm
  preimage_map := moduleHomOfExtensionNatTransOn_map.{w} b

include b in
/-- Extension of scalars to the module-valued functors on a domain of algebras with a base
object is full: this is what the library's proofs of [Stacks, Tags 06V2 and 06V3] use on the full
domain of algebras, and what is otherwise missing on a restricted domain. -/
public lemma full_moduleExtensionFunctorOn : (moduleExtensionFunctorOn.{w} ι).Full :=
  (fullyFaithfulModuleExtensionFunctorOn.{w} b).full

include b in
/-- Extension of scalars to the module-valued functors on a domain of algebras with a base
object is faithful. -/
public lemma faithful_moduleExtensionFunctorOn : (moduleExtensionFunctorOn.{w} ι).Faithful :=
  (fullyFaithfulModuleExtensionFunctorOn.{w} b).faithful

end Full

/-! ### The base object of the algebras of a site -/

namespace BaseAlgebraObject

/-- The base ring is a weakly initial object of the algebras of a site as soon as its spectrum
is an object of the site. No size bound beyond that hypothesis is needed: the object is `A`
itself, and the comparison with the lifted base ring is the canonical algebra equivalence. -/
public def siteOfSpecMem {A : Type u} [CommRing A] (P : ObjectProperty Scheme.{u})
    (hA : P (Spec (CommRingCat.of A))) :
    BaseAlgebraObject.{u} (siteAlgebraInclusion.{u, u} A P) where
  base := ⟨CommAlgCat.of A A, hA⟩
  equiv := ULift.algEquiv.symm
  hom X := ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId A X.obj))

end BaseAlgebraObject

end AdequateFunctor

end
