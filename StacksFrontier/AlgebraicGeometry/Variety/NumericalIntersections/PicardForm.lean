module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intersection number as a multilinear form on the Picard group

Let `k` be a field, `X` a proper scheme over `k` and `i : Z ⟶ X` a closed subscheme of dimension
at most `d`. The intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` of [Stacks, Tag 0BEP]
(`AlgebraicGeometry.intersectionNumber`) depends on each `𝓛_j` only through its isomorphism
class, and it is additive in each slot ([Stacks, Tag 0BER],
`AlgebraicGeometry.intersectionNumber_tensor`). It therefore descends to a `ℤ`-multilinear form

`Pic(X) × ⋯ × Pic(X) → ℤ`

on `d` copies of the Picard group, which is what this file constructs. Its value on the classes
of invertible modules is their intersection number
(`AlgebraicGeometry.picardIntersection_picardClass`).

This is the form in which the intersection number is used to show that the degree of an
endomorphism of an abelian variety is a polynomial function of degree at most `2 g`: the classes
`[(∑ c_k a_k)^* L]` satisfy the cube relation, and a multilinear form evaluated along a map with
the cube relation is polynomial (`Stacks.QuadraticMap.exists_mvPolynomial_multilinear_eq`).

## Main definitions

* `AlgebraicGeometry.picardRep` — the module `Stacks.Picard.picardRepresentative` of a class.
* `AlgebraicGeometry.picardIntersection` — the intersection number as a multilinear form on
  `Pic(X)`.

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_of_forall_iso` — the intersection number depends
  only on the isomorphism classes of the modules.
* `AlgebraicGeometry.picardIntersection_picardClass` — the form on classes of modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))

/-- **The intersection number depends only on the isomorphism classes of the modules.** If
`L q ≅ M q` for every `q`, then `(L_1 ⋯ L_d · Z) = (M_1 ⋯ M_d · Z)`. The slots are replaced one at
a time (`AlgebraicGeometry.intersectionNumber_eq_of_iso_at`). -/
theorem intersectionNumber_eq_of_forall_iso (L M : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (e : ∀ q, Nonempty (L q ≅ M q)) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  classical
  let F : Finset (Fin d) → Fin d → X.Modules := fun s q => if q ∈ s then M q else L q
  have hF : ∀ s q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F s q) := by
    intro s q
    by_cases h : q ∈ s
    · simp only [F, ite_eq_left h]; infer_instance
    · simp only [F, ite_eq_right h]; infer_instance
  have key : ∀ s : Finset (Fin d),
      intersectionNumber k f i d hd (F ∅) = intersectionNumber k f i d hd (F s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s has ih =>
      refine ih.trans (intersectionNumber_eq_of_iso_at k f i d hd _ _ a (fun q hq => ?_) ?_)
      · simp [F, Finset.mem_insert, hq]
      · exact eqToIso (by simp [F, has]) ≪≫ (e a).some ≪≫ eqToIso (by simp [F])
  have h0 : F ∅ = L := funext fun q => by simp [F]
  have h1 : F Finset.univ = M := funext fun q => by simp [F]
  rw [← intersectionNumber_congr_family k f i d hd h0,
    ← intersectionNumber_congr_family k f i d hd h1]
  exact key Finset.univ

/-- The representative `Stacks.Picard.picardRepresentative` of a class in `Pic(X)`, as an
`𝒪_X`-module. -/
abbrev picardRep (x : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) : X.Modules :=
  (Stacks.Picard.picardRepresentative X.toRingedSpace x).obj

/-- The representative `AlgebraicGeometry.picardRep x` of a class in `Pic(X)` is invertible. -/
instance isInvertible_picardRep
    (x : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (picardRep x) :=
  (Stacks.Picard.picardRepresentative X.toRingedSpace x).property

/-- The class of the representative is the class represented. -/
theorem picardClass_picardRep (x : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf (picardRep x)
      (isInvertible_picardRep x) = x :=
  Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x

/-- The representative of `x` is isomorphic to any invertible module whose class is `x`. -/
private theorem nonempty_picardRep_iso_of_picardClass_eq
    (x : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (h : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL = x) :
    Nonempty (picardRep x ≅ L) :=
  (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _
    (isInvertible_picardRep _) hL).mp (by rw [picardClass_picardRep, h])

/-- The representative of a class is isomorphic to any invertible module of that class. -/
theorem nonempty_picardRep_picardClass_iso (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) :
    Nonempty (picardRep (Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL) ≅ L) :=
  nonempty_picardRep_iso_of_picardClass_eq _ L hL rfl

/-- The intersection number of the representatives of a family of classes. -/
def picardIntersectionFun
    (x : Fin d → Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) : ℤ :=
  intersectionNumber k f i d hd fun q => picardRep (x q)

/-- **Additivity in each slot**, from [Stacks, Tag 0BER]. -/
theorem picardIntersectionFun_update_add [DecidableEq (Fin d)]
    (x : Fin d → Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) (j : Fin d)
    (a b : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    picardIntersectionFun k f i d hd (Function.update x j (a + b)) =
      picardIntersectionFun k f i d hd (Function.update x j a) +
        picardIntersectionFun k f i d hd (Function.update x j b) := by
  have ha := isInvertible_picardRep a
  have hb := isInvertible_picardRep b
  have hab := nonempty_picardRep_iso_of_picardClass_eq (a + b)
    (Stacks.SheafOfModules.schemeTensor X (picardRep a) (picardRep b))
    (Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ ha hb)
    (by rw [Stacks.SheafOfModules.picardClass_schemeTensor X _ _ ha hb, picardClass_picardRep,
      picardClass_picardRep])
  refine intersectionNumber_tensor k f i d hd j _ _ _ (fun q hq => ?_) (fun q hq => ?_) ?_
  · simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne hq]
  · exact eqToIso (by simp) ≪≫ hab.some ≪≫ eqToIso (by simp only [Function.update_self]; rfl)

/-- **The intersection number as a multilinear form on the Picard group.** For a proper scheme
`X` over a field `k` and a closed subscheme `Z` of dimension at most `d`, the map
`([𝓛_1], …, [𝓛_d]) ↦ (𝓛_1 ⋯ 𝓛_d · Z)` is a well defined `ℤ`-multilinear form on `Pic(X)^d`
([Stacks, Tags 0BEP, 0BER]). -/
@[sga "6 X 4.4" "partial"]
def picardIntersection :
    MultilinearMap ℤ
      (fun _ : Fin d => Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) ℤ where
  toFun := picardIntersectionFun k f i d hd
  map_update_add' x j a b := by
    convert picardIntersectionFun_update_add k f i d hd x j a b
  map_update_smul' x j c a := by
    let φ : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf →+ ℤ :=
      AddMonoidHom.mk' (fun a => picardIntersectionFun k f i d hd (Function.update x j a))
        (fun a b => picardIntersectionFun_update_add k f i d hd x j a b)
    exact φ.map_zsmul c a

/-- The form `AlgebraicGeometry.picardIntersection` evaluated at a family of classes is the
intersection number of their representatives. -/
theorem picardIntersection_apply
    (x : Fin d → Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    picardIntersection k f i d hd x = intersectionNumber k f i d hd fun q => picardRep (x q) :=
  rfl

/-- **The form on classes of modules is their intersection number.** -/
theorem picardIntersection_picardClass (L : Fin d → X.Modules)
    [hL : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    picardIntersection k f i d hd
        (fun q => Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf (L q) (hL q)) =
      intersectionNumber k f i d hd L :=
  intersectionNumber_eq_of_forall_iso k f i d hd _ _ fun q =>
    nonempty_picardRep_picardClass_iso (L q) (hL q)

end AlgebraicGeometry
