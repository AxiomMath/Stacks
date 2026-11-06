module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitCoprojections
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# A contravariant functor carries a derived colimit to a derived limit

Let `D` and `D'` be pre-triangulated categories and let `H : Dᵒᵖ ⥤ D'` be an additive functor
which carries distinguished triangles of `D` to distinguished triangles of `D'`, in the weak
"there is a connecting morphism" sense.  Let `(Kₙ, fₙ)` be a system of objects of `D` whose
direct sum exists and let `K = hocolim Kₙ`.  If the canonical comparison
`H(⊕ Kₙ) ⟶ ∏ₙ H(Kₙ)` is an isomorphism, then `H K = R lim H Kₙ`.

This is the formal half of [Stacks, Tag 0A0A]: there the system is a system of perfect objects
of `D(𝒪)`, `H` is `RSheafHom(-, E)` and the comparison isomorphism is the statement that derived
internal Hom out of a direct sum is the product of the derived internal Homs.  Nothing in the
argument uses any of that, only the two displayed properties of `H`, so it is recorded here for
pre-triangulated categories.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.of_natIso`: being a derived limit transports
  along an isomorphism of inverse systems.
* `CategoryTheory.Pretriangulated.IsDerivedLimit.of_isoObj`: being a derived limit of a fixed
  inverse system transports along an isomorphism of the limit *object*.
* `CategoryTheory.Pretriangulated.isDerivedLimit_of_isHomotopyColimit`: the image of a derived
  colimit under such an `H` is a derived limit of the image system.
* `CategoryTheory.Pretriangulated.exists_distTriang_pi_lift_map_coprojections`: the same, with
  the projections of the derived limit named as the images of the coprojections of the derived
  colimit — the conclusion that the bare existential cannot carry.

## Implementation notes

The hypothesis on triangles is the "there is a connecting morphism making the image a
distinguished triangle" form rather than a `CategoryTheory.Functor.IsTriangulated` instance,
because a contravariant derived internal Hom has no `CategoryTheory.Functor.CommShift` in this
development; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated`.  The two
morphisms of the image triangle are therefore named explicitly: a distinguished
`T = (X ⟶ Y ⟶ Z ⟶ X⟦1⟧)` is sent to `H Z ⟶ H Y ⟶ H X ⟶ (H Z)⟦1⟧`, whose first two maps are
`H T.mor₂` and `H T.mor₁`.

Additivity of `H` is what turns the difference map `1 - fₙ` of the defining triangle of the
derived colimit into the difference map `(hₙ) ↦ (hₙ - hₙ₊₁ ∘ H fₙ)` of the defining triangle of
the derived limit, and is used for nothing else.

The comparison morphism is `Limits.Pi.lift fun n ↦ H (ιₙ)`, the morphism whose `n`-th component
is the image of the `n`-th coprojection; assuming it invertible is the statement
`H(⊕ Kₙ) = ∏ H(Kₙ)` *with its canonical map*, which is what the comparison of triangles needs.
Assuming merely that the two objects are isomorphic would not suffice.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Transport along an isomorphism of systems -/

/-- A distinguished triangle whose two last objects are transported along an isomorphism that
intertwines the middle maps stays distinguished. -/
private theorem mk_comp_hom_mem_distTriang {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A B B' : C} (e : B ≅ B') {p : A ⟶ B} {f : B ⟶ B} {g : B' ⟶ B'} {δ : B ⟶ A⟦(1 : ℤ)⟧}
    (hfg : f ≫ e.hom = e.hom ≫ g) (hδ : Triangle.mk p f δ ∈ distTriang C) :
    Triangle.mk (p ≫ e.hom) g (e.inv ≫ δ) ∈ distTriang C :=
  isomorphic_distinguished _ hδ _
    (Triangle.isoMk _ _ (Iso.refl A) e.symm e.symm (by simp [Triangle.mk])
      (by
        simpa [Triangle.mk] using (by rw [Iso.comp_inv_eq, Category.assoc, hfg,
          Iso.inv_hom_id_assoc] : g ≫ e.inv = e.inv ≫ f)) (by simp [Triangle.mk]))

/-- **Being a derived limit transports along an isomorphism of the limit object.** The triangle
`K ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ K⟦1⟧` witnessing `K = R lim Fₙ` is isomorphic, by an isomorphism which is the
identity on the two copies of the product, to the corresponding triangle on `K'`.

This is the companion of `CategoryTheory.Pretriangulated.IsDerivedLimit.of_natIso`, which
transports along an isomorphism of the *system*. -/
theorem IsDerivedLimit.of_isoObj {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj (op n)]
    {K K' : D} (e : K ≅ K') (hK : IsDerivedLimit F K) : IsDerivedLimit F K' := by
  obtain ⟨p, δ, hδ⟩ := hK
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom, ?_⟩
  exact isomorphic_distinguished _ hδ _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) (by simp [Triangle.mk])
      (by simp [Triangle.mk]) (by simp [Triangle.mk]))

/-- **Being a derived limit transports along an isomorphism of inverse systems.**  If `F ≅ G` as
functors `ℕᵒᵖ ⥤ D` and `K = R lim Fₙ`, then `K = R lim Gₙ`.

The isomorphism of systems induces an isomorphism `∏ Fₙ ≅ ∏ Gₙ` of the products which
intertwines the two difference maps, so the triangle witnessing `K = R lim Fₙ` is isomorphic to
one of the shape witnessing `K = R lim Gₙ`. -/
theorem IsDerivedLimit.of_natIso {F G : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun n : ℕ ↦ G.obj (op n)]
    (c : F ≅ G) {K : D} (hK : IsDerivedLimit F K) : IsDerivedLimit G K := by
  let c' : Discrete.functor (fun n : ℕ ↦ F.obj (op n)) ≅
      Discrete.functor (fun n : ℕ ↦ G.obj (op n)) :=
    Discrete.natIso fun n ↦ c.app (op n.as)
  let e := HasLimit.isoOfNatIso c'
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n =
      Pi.π (fun n : ℕ ↦ F.obj (op n)) n ≫ c.hom.app (op n) :=
    HasLimit.isoOfNatIso_hom_π c' ⟨n⟩
  let bF := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
    Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let bG := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj (op n)) n -
    Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op
  have hb : bF ≫ e.hom = e.hom ≫ bG := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [bF, bG, Category.assoc, he, Pi.lift_comp_π, Preadditive.comp_sub]
    rw [← Category.assoc e.hom, he, Category.assoc,
      ← c.hom.naturality (homOfLE (Nat.le_succ n)).op, ← Category.assoc, Pi.lift_comp_π,
      Preadditive.sub_comp, Category.assoc]
  obtain ⟨p, δ, hδ⟩ := hK
  exact ⟨p ≫ e.hom, e.inv ≫ δ, mk_comp_hom_mem_distTriang e hb hδ⟩

/-! ### The image of a derived colimit -/

section Contravariant

variable {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- **A contravariant functor carries a derived colimit datum to a derived limit presentation
whose projections are named.**  Let `H : Dᵒᵖ ⥤ D'` be additive, let it carry every distinguished
triangle of `D` to a distinguished triangle of `D'` in the sense of `hH` below, and let
`(K, iₙ, c)` be a derived colimit datum for a system `F : ℕ ⥤ D` whose direct sum exists.  If the
canonical comparison `H(⊕ Kₙ) ⟶ ∏ H(Kₙ)` is an isomorphism, then the images `H(iₙ)` of the
coprojections are the projections of a derived-limit presentation of the image system at
`H K`: their product is the first map of a distinguished Milnor triangle.

This is the form [Stacks, Tag 0CRH] is for.  The structural map of the triangle produced below is
`H(Sigma.desc i) ≫ e`, whose `n`-th component is `H(iₙ)` because `iₙ = σₙ ≫ Sigma.desc i`; a
presentation whose structural map is existentially quantified, as in
`CategoryTheory.Pretriangulated.isDerivedLimit_of_isHomotopyColimit`, carries no such
information.  The conclusion is stated as the distinguished triangle itself rather than through
`NoetherianAdicCompletion.IsDerivedLimitWithProjections`, which is the same statement but lives
in a far larger import closure; it is that predicate on the nose, so a consumer crosses by
`exact`. -/
theorem exists_distTriang_pi_lift_map_coprojections (H : Dᵒᵖ ⥤ D') [H.Additive] (F : ℕ ⥤ D)
    [HasCoproduct F.obj] [HasProduct fun n : ℕ ↦ (F.op ⋙ H).obj (op n)]
    (hH : ∀ T : Triangle D, T ∈ distTriang D →
      ∃ δ : H.obj (op T.obj₁) ⟶ (H.obj (op T.obj₃))⟦(1 : ℤ)⟧,
        Triangle.mk (H.map T.mor₂.op) (H.map T.mor₁.op) δ ∈ distTriang D')
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦ H.map (Sigma.ι F.obj n).op) :
      H.obj (op (∐ F.obj)) ⟶ ∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n)))
    {K : D} {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (hK : IsHomotopyColimitWithCoprojections F K i c) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) ⟶ (H.obj (op K))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift (fun n : ℕ ↦ H.map (i n).op) :
          H.obj (op K) ⟶ ∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n))
        (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) n -
          Pi.π (fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) (n + 1) ≫
            (F.op ⋙ H).map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang D' := by
  obtain ⟨δ, hδ⟩ := hH _ hK.mem_distTriang
  let e : H.obj (op (∐ F.obj)) ≅ ∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n) :=
    @asIso _ _ _ _ _ hcomp
  have he (n : ℕ) :
      e.hom ≫ Pi.π (fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) n = H.map (Sigma.ι F.obj n).op :=
    Pi.lift_comp_π _ _
  let d : ∐ F.obj ⟶ ∐ F.obj := Sigma.desc fun n ↦ Sigma.ι F.obj n -
    F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)
  let b := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) n -
    Pi.π (fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) (n + 1) ≫
      (F.op ⋙ H).map (homOfLE (Nat.le_succ n)).op
  have hb : H.map d.op ≫ e.hom = e.hom ≫ b := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, he, ← H.map_comp, ← op_comp]
    dsimp only [d]
    rw [Sigma.ι_desc, op_sub, op_comp, H.map_sub, H.map_comp]
    simp only [b, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, he]
    rw [← Category.assoc, he]
    rfl
  have hkey : (Pi.lift (fun n : ℕ ↦ H.map (i n).op) :
        H.obj (op K) ⟶ ∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n)) =
      H.map (Sigma.desc i).op ≫ e.hom := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Pi.lift_comp_π, Category.assoc, he n, ← H.map_comp, ← op_comp, Sigma.ι_desc]
  refine ⟨e.inv ≫ δ, ?_⟩
  rw [hkey]
  exact mk_comp_hom_mem_distTriang e hb hδ

/-- **A contravariant functor carries a derived colimit to a derived limit.**  Let
`H : Dᵒᵖ ⥤ D'` be additive, let it carry every distinguished triangle of `D` to a distinguished
triangle of `D'` in the sense of `hH` below, and let `K = hocolim Kₙ` for a system `F : ℕ ⥤ D`
whose direct sum exists.  If the canonical comparison `H(⊕ Kₙ) ⟶ ∏ H(Kₙ)` is an isomorphism then
`H K = R lim H Kₙ`.

The triangle `⊕ Kₙ → ⊕ Kₙ → K → (⊕ Kₙ)⟦1⟧` witnessing the derived colimit is carried by `H` to a
distinguished triangle `H K → H(⊕ Kₙ) → H(⊕ Kₙ) → (H K)⟦1⟧`; transporting its two outer objects
along the comparison isomorphism turns its middle map, the image of `1 - fₙ`, into the difference
map of the image system, by additivity of `H` and the universal property of the direct sum.  This
is `CategoryTheory.Pretriangulated.exists_distTriang_pi_lift_map_coprojections` with the
projections forgotten. -/
theorem isDerivedLimit_of_isHomotopyColimit (H : Dᵒᵖ ⥤ D') [H.Additive] (F : ℕ ⥤ D)
    [HasCoproduct F.obj] [HasProduct fun n : ℕ ↦ (F.op ⋙ H).obj (op n)]
    (hH : ∀ T : Triangle D, T ∈ distTriang D →
      ∃ δ : H.obj (op T.obj₁) ⟶ (H.obj (op T.obj₃))⟦(1 : ℤ)⟧,
        Triangle.mk (H.map T.mor₂.op) (H.map T.mor₁.op) δ ∈ distTriang D')
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦ H.map (Sigma.ι F.obj n).op) :
      H.obj (op (∐ F.obj)) ⟶ ∏ᶜ fun n : ℕ ↦ (F.op ⋙ H).obj (op n)))
    {K : D} (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (F.op ⋙ H) (H.obj (op K)) := by
  obtain ⟨i, c, hK'⟩ := hK.exists_coprojections
  obtain ⟨δ, hδ⟩ := exists_distTriang_pi_lift_map_coprojections H F hH hcomp hK'
  exact ⟨_, δ, hδ⟩

end Contravariant

end CategoryTheory.Pretriangulated

end
