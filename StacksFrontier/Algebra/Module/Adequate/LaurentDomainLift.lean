module

public import StacksFrontier.Algebra.Module.Adequate.DomainValues
public import StacksFrontier.Algebra.Module.Adequate.LaurentLargeLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting an additive transformation to a module map on a restricted domain of algebras

[Stacks, Tag 06V5] says that an additive natural transformation of module-valued functors which
is semilinear for the *units* of the structure ring is already induced by a morphism of
module-valued functors, as soon as the target commutes with flat base change.
`AdequateFunctor.Laurent.naturalTransformation_lifts_of_units_of_flatBaseChange_large` proves
this for functors defined on *all* commutative `A`-algebras. This file carries it to functors
defined only on a full subcategory `Q` of those algebras, which is the domain shape of
`AdequateFunctor.siteAlgebraInclusion`: an object is an algebra together with a proof that it
satisfies `Q`, and a morphism is an algebra map, so nothing is ever transported along an
isomorphism of algebras.

The mathematical content is unchanged. At the algebra `B` where semilinearity in a scalar `b` is
being tested, adjoining a root `r` of `X ^ 2 - b * X + 1` writes `b` as the sum of the two units
`r` and `b - r`; semilinearity for units gives the identity over `B[r]`, and `B → B[r]` is
faithfully flat, so the identity descends to `B`.

## Main results

* `AdequateFunctor.LaurentDomain.naturalTransformation_lifts_of_units_of_flatBaseChange` —
  [Stacks, Tag 06V5] for module-valued functors on a restricted domain of algebras.

## Implementation notes

The root extension is the only algebra the argument builds, and on a restricted domain it is not
available for free: the object of `Q.FullSubcategory` carried by `AdjoinRoot p` exists only once
`AdjoinRoot p` is known to satisfy `Q`. The theorem therefore carries the closure hypothesis
`hadj`, and it is load-bearing. It is consumed exactly once, to produce
`hS : Q (CommAlgCat.of A S)` for `S = AdjoinRoot p`; that proof is the second component of the
object `B'` at which the unit decomposition of `b` is read off, hence of the morphism
`f : op (op Z) ⟶ B'` carried by `B → B[r]`. The flat-base-change hypothesis `hbase` is then
applied at that single morphism `f` and nowhere else, so `hadj` is precisely what makes the one
use of `hbase` expressible.

The `Algebra A (AdjoinRoot p)` instance is supplied explicitly in `hadj`, as the restriction of
scalars along `algebraMap A B` of the canonical `B`-algebra structure, because that is the
instance the proof puts on `S`; a propositionally equal but definitionally different instance
would give a different object of `CommAlgCat A`, and the membership assumed would not be the
membership needed. This costs a caller nothing: the underlying ring of
`CommAlgCat.of A (AdjoinRoot p)` is `AdjoinRoot p` for every `A`-algebra structure on it, so a
property of algebras that reads only the underlying ring — as the size bound of
`AdequateFunctor.size_lt_of_spec_adjoinRoot` does — discharges `hadj` for this instance just as
for any other.

Like `AdequateFunctor.LaurentDomain.PreservesFlatBaseChange`, the hypothesis `hbase` quantifies
only over morphisms *internal to the domain*, which is weaker than the condition over all
algebra maps and is all the proof consumes.

## References

* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
-/

@[expose] public section

namespace AdequateFunctor.LaurentDomain

section

open CategoryTheory Opposite
open scoped TensorProduct

universe w v u u₁ v₁

/-- The commutative rings underlying the algebras of a chosen domain of `A`-algebras: the
functor `AdequateFunctor.algebraRingDiagramOn` before commutativity is forgotten. Flat base
change is stated in this form, the tensor product and the flatness of a ring map both being
taken over commutative rings. -/
@[sga "3 VIIB 1.2.1" "more general"]
public abbrev algebraCommRingDiagramOn {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A) :
    (Cᵒᵖ)ᵒᵖ ⥤ CommRingCat.{max u v} :=
  ι.op.op ⋙ Laurent.algebraCommRingDiagramLarge.{v} A

attribute [local instance 0] CategoryTheory.ReflQuiver.toQuiver

/-- An additive natural transformation of module-valued functors on a restricted domain of
algebras which commutes with multiplication by units is induced by a morphism of module-valued
functors, provided the target commutes with flat base change along the morphisms of the domain
and the domain is closed under adjoining a root of a polynomial. This is [Stacks, Tag 06V5] on
such a domain.

No `@[stacks]` attribute is placed here: this is Tag 06V5 carried to a restricted
domain, not a further part of that tag's covering set. -/
public theorem naturalTransformation_lifts_of_units_of_flatBaseChange
    (A : Type u) [CommRing A] (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (hadj : ∀ (R : Type (max u v)) [CommRing R] [Algebra A R], Q (CommAlgCat.of A R) →
      ∀ p : Polynomial R,
        Q (@CommAlgCat.of A _ (AdjoinRoot p) _
          (RingHom.toAlgebra ((algebraMap R (AdjoinRoot p)).comp (algebraMap A R)))))
    (F G : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (φ : F.presheaf ⟶ G.presheaf)
    (hunit : ∀ (X : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ) (x : F.obj X)
      (a : Units ((algebraRingDiagramOn Q.ι).obj X)),
      φ.app X ((a : (algebraRingDiagramOn Q.ι).obj X) • x) =
        (a : (algebraRingDiagramOn Q.ι).obj X) • (φ.app X x : G.obj X))
    (hbase : ∀ {X Y : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ} (f : X ⟶ Y),
      letI : Algebra ((algebraCommRingDiagramOn Q.ι).obj X)
          ((algebraCommRingDiagramOn Q.ι).obj Y) :=
        ((algebraCommRingDiagramOn Q.ι).map f).hom.toAlgebra
      Module.Flat ((algebraCommRingDiagramOn Q.ι).obj X)
          ((algebraCommRingDiagramOn Q.ι).obj Y) →
        ∃ e : TensorProduct ((algebraCommRingDiagramOn Q.ι).obj X)
              ((algebraCommRingDiagramOn Q.ι).obj Y) (G.obj X) ≃ₗ[
                (algebraCommRingDiagramOn Q.ι).obj Y] G.obj Y,
          ∀ x : G.obj X,
            e ((1 : (algebraCommRingDiagramOn Q.ι).obj Y) ⊗ₜ[
              (algebraCommRingDiagramOn Q.ι).obj X] x) = G.map f x) :
    ∃ ψ : F ⟶ G,
      (PresheafOfModules.toPresheaf (algebraRingDiagramOn Q.ι)).map ψ = φ := by
  let ψ : F ⟶ G :=
    { app := fun Z ↦
        ModuleCat.ofHom
        { toFun := φ.app Z
          map_add' := (φ.app Z).hom.map_add
          map_smul' := by
            intro b x
            rcases Z with ⟨⟨Z⟩⟩
            change ↥Z.obj at b
            rcases subsingleton_or_nontrivial ↥Z.obj with hR | hR
            · have := Module.subsingleton ↥Z.obj (G.obj (op (op Z)))
              exact Subsingleton.elim _ _
            let p : Polynomial ↥Z.obj := Polynomial.X ^ 2 -
              Polynomial.C b * Polynomial.X + 1
            have hpdeg : p.IsMonicOfDegree 2 := Polynomial.isMonicOfDegree_sub_add_two b 1
            have hp : p.Monic := hpdeg.monic
            let S := AdjoinRoot p
            let algAS : Algebra A S :=
              ((algebraMap ↥Z.obj S).comp (algebraMap A ↥Z.obj)).toAlgebra
            have hS : Q (CommAlgCat.of A S) := hadj ↥Z.obj Z.property p
            let g : ↥Z.obj →ₐ[A] S :=
              { algebraMap ↥Z.obj S with commutes' := fun _ ↦ rfl }
            let B' : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ :=
              op (op (⟨CommAlgCat.of A S, hS⟩ : Q.FullSubcategory))
            let f : op (op Z) ⟶ B' :=
              (ObjectProperty.homMk (X := Z)
                (Y := (⟨CommAlgCat.of A S, hS⟩ : Q.FullSubcategory))
                (CommAlgCat.ofHom g)).op.op
            let r : S := AdjoinRoot.root p
            have hr : r * (algebraMap ↥Z.obj S b - r) = 1 := by
              have hroot : r ^ 2 - algebraMap ↥Z.obj S b * r + 1 = 0 := by
                simpa only [p, map_add, map_sub, map_pow, map_mul, Polynomial.aeval_X,
                  Polynomial.aeval_C, map_one] using
                  (AdjoinRoot.aeval_eq p).trans AdjoinRoot.mk_self
              linear_combination -hroot
            have hr' : (algebraMap ↥Z.obj S b - r) * r = 1 := (mul_comm _ _).trans hr
            let ur : Units S := ⟨r, algebraMap ↥Z.obj S b - r, hr, hr'⟩
            let us : Units S := ⟨algebraMap ↥Z.obj S b - r, r, hr', hr⟩
            have hsum : (ur : S) + (us : S) = algebraMap ↥Z.obj S b := add_sub_cancel _ _
            have hff₀ : (algebraMap ↥Z.obj S).FaithfullyFlat := by
              have : Module.Free ↥Z.obj S := hp.free_adjoinRoot
              have : Nontrivial S := (AdjoinRoot.of.injective_of_monic_of_degree_pos hp (by
                  rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpdeg.natDegree_eq]
                  norm_num)).nontrivial
              rw [RingHom.faithfullyFlat_algebraMap_iff]
              infer_instance
            let q := ((algebraCommRingDiagramOn Q.ι).map f).hom
            have hq : q = algebraMap ↥Z.obj S := rfl
            have hff : q.FaithfullyFlat := hff₀
            let : Algebra ((algebraCommRingDiagramOn Q.ι).obj (op (op Z)))
                ((algebraCommRingDiagramOn Q.ι).obj B') := q.toAlgebra
            obtain ⟨e, he⟩ := hbase f hff.flat
            have hinj : Function.Injective (fun y : G.obj (op (op Z)) ↦
                e (1 ⊗ₜ[↑((algebraCommRingDiagramOn Q.ι).obj (op (op Z)))] y)) :=
              e.injective.comp
                (faithfullyFlat_tensor_mk_injective q hff (G.obj (op (op Z))))
            have hGinj : Function.Injective (G.map f) := fun y z hyz ↦ hinj <| by
              dsimp only
              rwa [he y, he z]
            have hnat (z : F.obj (op (op Z))) :
                φ.app B' (F.map f z) = G.map f (φ.app (op (op Z)) z) :=
              ConcreteCategory.congr_hom (φ.naturality f) z
            apply hGinj
            rw [← hnat (b • x), F.map_smul]
            simp only [RingHom.id_apply]
            let y : G.obj (op (op Z)) := φ.app (op (op Z)) x
            show φ.app B' ((algebraRingDiagramOn Q.ι).map f b • F.map f x) =
              G.map f (b • y)
            rw [G.map_smul]
            let φ' : F.obj B' →+ G.obj B' :=
              { toFun := fun z ↦ φ.app B' z
                map_zero' := (φ.app B').hom.map_zero
                map_add' := (φ.app B').hom.map_add }
            show φ' (q b • F.map f x) = q b • G.map f y
            rw [hq]
            -- `φ'` bundles `φ.app B'` so that the scalar action on `G.obj B'`
            -- resolves; the cost is that `hunit` and `hnat`, stated for
            -- `φ.app B'`, no longer match syntactically under its coercion, and
            -- their scalar actions come from a different (defeq) instance path.
            -- Restating each step in the goal's own spelling and discharging it
            -- by a *term* lets definitional unification absorb that.
            have hunit' (u : Units S) :
                φ' ((u : S) • F.map f x) = (u : S) • φ' (F.map f x) :=
              hunit B' (F.map f x) u
            have hu : φ' ((algebraMap ↥Z.obj S b) • F.map f x) =
                (algebraMap ↥Z.obj S b) • φ' (F.map f x) := by
              rw [← hsum, add_smul, add_smul, ← hunit' ur, ← hunit' us]
              exact φ'.map_add _ _
            have hnat' : φ' (F.map f x) = G.map f y := hnat x
            rw [hu, hnat']
            rfl }
      naturality := by
        intro X Y f
        ext x
        exact CategoryTheory.congr_fun (φ.naturality f) x }
  exact ⟨ψ, rfl⟩

end

end AdequateFunctor.LaurentDomain

end
