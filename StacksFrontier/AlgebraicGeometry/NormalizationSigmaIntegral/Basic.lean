module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# A finite coproduct of integral morphisms is integral

If `V : I → Scheme` is a family indexed by a finite type and `q i : V i ⟶ S` is integral for
every `i`, then the induced morphism `∐ V ⟶ S` is integral.

Integrality of a morphism of schemes is not local on the source, so this is not an instance of
the Zariski-local-at-source machinery. It is proved by induction on the finite index type. The
inductive step splits `∐ (V : Option I → Scheme)` as `V none ⨿ ∐ (V ∘ some)`, where the binary
case is already available by instance search.

## Main results

* `AlgebraicGeometry.isIntegralHom_of_isIntegralHom_iso_comp` transports integrality backwards
  along an isomorphism of the source.
* `AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite'`: a coproduct of finitely many integral
  morphisms to a common target is integral.

## Implementation notes

Both transports along an isomorphism compose with the isomorphism's inverse, which is itself
integral because an isomorphism is a closed immersion. They do not use
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`, because instance search does not
find `CategoryTheory.MorphismProperty.RespectsIso` for `AlgebraicGeometry.IsIntegralHom` at this
pin; the error it gives names the missing `RespectsIso` instance rather
than the property it is about.

The isomorphism `V none ⨿ ∐ (V ∘ some) ≅ ∐ V` is built here with its four coprojection
identities stated as separate hypotheses and its two identity laws proved by explicit rewriting.
Proving those laws by `simp` leaves two goals unsolved: `simp` distributes the composite over
`CategoryTheory.Limits.coprod.desc` before reducing the coprojections, and the normal form it
reaches is no longer in the shape `CategoryTheory.Limits.coprod.inl_desc` matches.

No `@[stacks]` attribute is attached. The statement is an auxiliary closure property used inside
the proofs of Tags 035L and 035Q rather than the content of a tag of its own, and no Stacks tag
states it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Transport integrality backwards along an isomorphism of the source, by composing with the
inverse, which is integral because an isomorphism is a closed immersion. -/
public theorem isIntegralHom_of_isIntegralHom_iso_comp {T V S : Scheme.{u}} (e : T ≅ V)
    (f : V ⟶ S) (h : IsIntegralHom (e.hom ≫ f)) : IsIntegralHom f :=
  e.inv_hom_id_assoc f ▸ inferInstanceAs (IsIntegralHom (e.inv ≫ e.hom ≫ f))

/-- A coproduct of finitely many integral morphisms to a common target is integral.

`AlgebraicGeometry.isIntegralHom_sigmaDesc` is the statement for an arbitrary index type under a
local finiteness hypothesis on the family, and
`AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite` its specialisation to a finite index type;
the prime here records that this form asks nothing of the index type beyond finiteness, in
particular no `Small` instance, and is proved directly by induction on it. -/
public theorem isIntegralHom_sigmaDesc_of_finite' {I : Type u} [Finite I]
    {V : I → Scheme.{u}} {S : Scheme.{u}} (q : ∀ i, V i ⟶ S)
    [∀ i, IsIntegralHom (q i)] : IsIntegralHom (Sigma.desc q) := by
  classical
  induction I using Finite.induction_empty_option with
  | @of_equiv I J e ih =>
    have : ∀ i, IsIntegralHom (q (e i)) := fun i ↦ inferInstance
    refine isIntegralHom_of_isIntegralHom_iso_comp (Sigma.reindex e V) _ ?_
    have he : (Sigma.reindex e V).hom ≫ Sigma.desc q =
        Sigma.desc (fun i ↦ q (e i)) := by
      ext i
      rw [← Category.assoc, Sigma.ι_reindex_hom, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    rw [he]
    exact ih (V := V ∘ e) (fun i ↦ q (e i))
  | h_empty =>
    have : IsEmpty (∐ V : Scheme) := Function.isEmpty (sigmaMk V).symm
    infer_instance
  | @h_option I _ ih =>
    let fwd : (V none ⨿ (∐ fun i ↦ V (some i)) : Scheme.{u}) ⟶ ∐ V :=
      coprod.desc (Sigma.ι V none) (Sigma.desc fun i ↦ Sigma.ι V (some i))
    let bwd : (∐ V : Scheme.{u}) ⟶ V none ⨿ (∐ fun i ↦ V (some i)) :=
      Sigma.desc fun i ↦ match i with
        | none => coprod.inl
        | some i => Sigma.ι (fun i ↦ V (some i)) i ≫ coprod.inr
    have hinl : coprod.inl ≫ fwd = Sigma.ι V none := coprod.inl_desc _ _
    have hinr : coprod.inr ≫ fwd = Sigma.desc fun i ↦ Sigma.ι V (some i) :=
      coprod.inr_desc _ _
    have hnone : Sigma.ι V none ≫ bwd = coprod.inl := Sigma.ι_comp_desc _ _
    have hsome (i : I) : Sigma.ι V (some i) ≫ bwd =
        Sigma.ι (fun i ↦ V (some i)) i ≫ coprod.inr := Sigma.ι_comp_desc _ _
    have hdescbwd : (Sigma.desc fun i ↦ Sigma.ι V (some i)) ≫ bwd = coprod.inr := by
      ext i
      simp [hsome]
    let e : (V none ⨿ (∐ fun i ↦ V (some i)) : Scheme.{u}) ≅ ∐ V :=
      { hom := fwd
        inv := bwd
        hom_inv_id := by
          apply coprod.hom_ext
          · rw [← Category.assoc, hinl, hnone, Category.comp_id]
          · rw [← Category.assoc, hinr, hdescbwd, Category.comp_id]
        inv_hom_id := by
          apply Sigma.hom_ext
          intro i
          cases i with
          | none => rw [← Category.assoc, hnone, hinl, Category.comp_id]
          | some i =>
            rw [← Category.assoc, hsome, Category.assoc, hinr, Sigma.ι_comp_desc,
              Category.comp_id] }
    refine isIntegralHom_of_isIntegralHom_iso_comp e _ ?_
    have he : e.hom ≫ Sigma.desc q =
        coprod.desc (q none) (Sigma.desc fun i ↦ q (some i)) := by
      apply coprod.hom_ext
      · rw [← Category.assoc, show coprod.inl ≫ e.hom = Sigma.ι V none from hinl,
          Sigma.ι_comp_desc, coprod.inl_desc]
      · rw [← Category.assoc,
          show coprod.inr ≫ e.hom = Sigma.desc (fun i ↦ Sigma.ι V (some i)) from hinr,
          coprod.inr_desc]
        ext i
        simp
    rw [he]
    have : IsIntegralHom (Sigma.desc fun i ↦ q (some i)) := ih (fun i ↦ q (some i))
    infer_instance

end AlgebraicGeometry

end
