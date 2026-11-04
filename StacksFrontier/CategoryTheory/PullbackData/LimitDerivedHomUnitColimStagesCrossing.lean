module

public import StacksFrontier.CategoryTheory.PullbackData.LimitSystemColimShift

/-!
# The colimit statement of Stacks 09RI transports across a crossing of pullback data

Let `P` and `Pm` be two pullback pseudofunctor data on the same category `A`, with fibres `D a`
and `Dm a`, and let `E a : Dm a ⥤ D a` be a family of fully faithful functors.  A *crossing* of
`Pm` into `P` along `E` is a family of isomorphisms

`κ_f : f^*_m ⋙ E a ≅ E b ⋙ f^*`,  `f : a ⟶ b`,

compatible with the comparisons of a presented factorisation on the two sides.  That
compatibility is the only hypothesis beyond the isomorphisms themselves, and it is exactly what
makes `κ` a morphism of pseudofunctors rather than a mere family of natural isomorphisms.

The point of this file is the transport: for a directed system `S` over a base `b`
(`CategoryTheory.PullbackData.LimitSystem`) and objects `Xm`, `Ym` of `Dm b`, the colimit
statement `CategoryTheory.PullbackData.LimitSystem.IsColim` for `Pm` at `Xm`, `Ym` and the one
for `P` at `E Xm`, `E Ym` are **the same statement**
(`CategoryTheory.PullbackData.Crossing.isColim_iff`).

## Why the compatibility is unavoidable

`CategoryTheory.PullbackData.LimitSystem.IsColim` is `Stacks.IsStagesColimit` for the transition
maps `CategoryTheory.PullbackData.LimitSystem.trans` and the maps to the vertex
`CategoryTheory.PullbackData.LimitSystem.projHom`, and both of those are
`CategoryTheory.PullbackData.factorHom` — conjugation of an inverse image by the comparison
`CategoryTheory.PullbackData.triangle` of a presented factorisation, that is by the datum's
composition comparison.  The only transport available for `Stacks.IsStagesColimit` is
`Stacks.IsStagesColimit.ofEquiv`, whose hypotheses `he` and `heT` are precisely that the
stagewise bijections intertwine the transition maps and the maps to the vertex of the two
systems.  So a transport of the colimit statement across `κ` is a transport of the two families
of conjugations, and that is `Crossing.iso_triangle`: no weaker compatibility suffices, because
with none at all the two systems of morphism sets are unrelated.  This is recorded here because
it is the shape every "compute the morphism groups in a model" argument meets.

## Main definitions

* `CategoryTheory.PullbackData.Crossing`: a crossing of two pullback pseudofunctor data along a
  family of functors — the isomorphisms and their compatibility with the comparisons of a
  presented factorisation.
* `CategoryTheory.PullbackData.Crossing.ofCompIso`: a crossing from its composition law at a
  composite, the presented factorisation being free.
* `CategoryTheory.PullbackData.Crossing.homEquiv`: the bijection of morphism sets it induces.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.isColim_of_equiv`: **the sharp transport** — the
  colimit statement for one datum follows from the one for the other as soon as the morphism
  groups at the stages and at the vertex are in bijection compatibly with the transition maps
  and the maps to the vertex, and those two families of squares are all that is needed.
* `CategoryTheory.PullbackData.Crossing.homEquiv_factorHom`: **the bijection intertwines the
  maps attached to a presented factorisation** — the content of the compatibility.
* `CategoryTheory.PullbackData.Crossing.isColim` and `isColim_iff`: **the colimit statement
  transports**, in both directions.
* `CategoryTheory.PullbackData.Crossing.shiftedIsColim`: the same at every shift of the first
  argument.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {Dm : A → Type u₃} [∀ a, Category.{v₃} (Dm a)]

namespace LimitSystem

/-- **The colimit statement of Stacks 09RI transports along stagewise bijections of morphism
groups.**  Let `Pm` and `P` be pullback pseudofunctor data on the same category, `S` a directed
system over a base `b`, `Xm`, `Ym` objects of `Dm b` and `X`, `Y` objects of `D b`.  If the
morphism groups of the two systems are in bijection at each stage and at the vertex, compatibly
with the transition maps `CategoryTheory.PullbackData.LimitSystem.trans` and the maps to the
vertex `CategoryTheory.PullbackData.LimitSystem.projHom`, then the colimit statement for `Pm` at
`Xm`, `Ym` gives the colimit statement for `P` at `X`, `Y`.

This is `Stacks.IsStagesColimit.ofEquiv` in the language of the system of Stacks 09RI, and it is
the *sharp* form of the transport: the two families of squares `he` and `heT` are exactly what is
needed, one for each pair `i ≤ j` of stages and one for each stage.  Nothing weaker can do,
because with no compatibility at all the two systems of morphism groups are unrelated; and
nothing stronger is needed, in particular no compatibility at a factorisation that the system
does not present.  Both `trans` and `projHom` are `CategoryTheory.PullbackData.factorHom` —
conjugation by the comparison of a presented factorisation, that is by the datum's composition
comparison — so `he` and `heT` are instances of a composition law for the bijections. -/
theorem isColim_of_equiv {Pm : PullbackData A Dm} {P : PullbackData A D} {b : A} {J : Type w}
    [Preorder J] (S : LimitSystem (A := A) b J) (Xm Ym : Dm b) (X Y : D b)
    (e : ∀ j : J, ((Pm.pull (S.toBase j)).obj Xm ⟶ (Pm.pull (S.toBase j)).obj Ym) ≃
      ((P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y))
    (eT : ((Pm.pull S.limitToBase).obj Xm ⟶ (Pm.pull S.limitToBase).obj Ym) ≃
      ((P.pull S.limitToBase).obj X ⟶ (P.pull S.limitToBase).obj Y))
    (he : ∀ (i j : J) (hij : i ≤ j)
        (s : (Pm.pull (S.toBase i)).obj Xm ⟶ (Pm.pull (S.toBase i)).obj Ym),
      e j (S.trans Pm Xm Ym i j hij s) = S.trans P X Y i j hij (e i s))
    (heT : ∀ (j : J) (s : (Pm.pull (S.toBase j)).obj Xm ⟶ (Pm.pull (S.toBase j)).obj Ym),
      eT (S.projHom Pm Xm Ym j s) = S.projHom P X Y j (e j s))
    (h : S.IsColim Pm Xm Ym) : S.IsColim P X Y :=
  Stacks.IsStagesColimit.ofEquiv _ _ (fun j => (e j).symm) eT.symm
    (fun i j hij s => (e j).symm_apply_eq.2
      ((he i j hij ((e i).symm s)).trans (congrArg (S.trans P X Y i j hij)
        ((e i).apply_symm_apply s))).symm)
    (fun j s => eT.symm_apply_eq.2
      ((heT j ((e j).symm s)).trans (congrArg (S.projHom P X Y j)
        ((e j).apply_symm_apply s))).symm)
    h

end LimitSystem

/-- **A crossing of the pullback pseudofunctor datum `Pm` into `P` along a family of functors
`E`**: for each morphism `f : a ⟶ b` of the base an isomorphism `f^*_m ⋙ E a ≅ E b ⋙ f^*`,
compatible with the comparisons of a presented factorisation on the two sides.

The second field is the composition law of the crossing.  It is what makes the family a morphism
of pseudofunctors, and it is what the transport of the colimit statement of Stacks 09RI needs;
see the module documentation. -/
structure Crossing (Pm : PullbackData A Dm) (P : PullbackData A D) (E : ∀ a : A, Dm a ⥤ D a) where
  /-- The crossing isomorphism at a morphism of the base. -/
  iso : ∀ {a b : A} (f : a ⟶ b), Pm.pull f ⋙ E a ≅ E b ⋙ P.pull f
  /-- **The composition law of the crossing**: at a presented factorisation `f ≫ g = k`, the
  crossing isomorphism at `k` read through the comparison of the factorisation for `P` is the
  image under `E` of the comparison for `Pm`, followed by the crossing isomorphisms at `g` and
  at `f`. -/
  iso_triangle : ∀ {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) (M : Dm c),
    (E a).map ((Pm.triangle hk).hom.app M) ≫ (iso f).hom.app ((Pm.pull g).obj M) ≫
        (P.pull f).map ((iso g).hom.app M) =
      (iso k).hom.app M ≫ (P.triangle hk).hom.app ((E c).obj M)

namespace Crossing

variable {Pm : PullbackData A Dm} {P : PullbackData A D} {E : ∀ a : A, Dm a ⥤ D a}
  (χ : Crossing Pm P E) (hE : ∀ a : A, (E a).FullyFaithful)

/-- **A crossing from its composition law at a composite.**  The comparison of a presented
factorisation `f ≫ g = k` is the composition comparison at `f`, `g` read through the
identification of the inverse image along `k` with the one along `f ≫ g`
(`CategoryTheory.PullbackData.triangle_rfl`), so the composition law need only be checked at the
composite itself.

This is the shape in which the composition law of a concrete crossing is proved: there the two
composition comparisons are named and the presented factorisation is not. -/
def ofCompIso (iso : ∀ {a b : A} (f : a ⟶ b), Pm.pull f ⋙ E a ≅ E b ⋙ P.pull f)
    (h : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (M : Dm c),
      (E a).map ((Pm.compIso f g).hom.app M) ≫ (iso f).hom.app ((Pm.pull g).obj M) ≫
          (P.pull f).map ((iso g).hom.app M) =
        (iso (f ≫ g)).hom.app M ≫ (P.compIso f g).hom.app ((E c).obj M)) :
    Crossing Pm P E where
  iso := iso
  iso_triangle := by
    intro a b c f g k hk M
    subst hk
    rw [Pm.triangle_rfl, P.triangle_rfl]
    exact h f g M

/-- **The bijection of morphism sets induced by a crossing**: morphisms between the inverse
images under `Pm` of `M` and `N` are morphisms between the inverse images under `P` of their
images under `E`.

The functors `E a` are fully faithful, so a morphism between the inverse images under `Pm` is the
same thing as a morphism between their images under `E a`; the crossing isomorphism identifies
those images with the inverse images under `P`. -/
def homEquiv {a b : A} (f : a ⟶ b) (M N : Dm b) :
    ((Pm.pull f).obj M ⟶ (Pm.pull f).obj N) ≃
      ((P.pull f).obj ((E b).obj M) ⟶ (P.pull f).obj ((E b).obj N)) :=
  (hE a).homEquiv.trans (Iso.homCongr ((χ.iso f).app M) ((χ.iso f).app N))

/-- `CategoryTheory.PullbackData.Crossing.homEquiv` written out. -/
theorem homEquiv_apply {a b : A} (f : a ⟶ b) (M N : Dm b)
    (φ : (Pm.pull f).obj M ⟶ (Pm.pull f).obj N) :
    χ.homEquiv hE f M N φ =
      (χ.iso f).inv.app M ≫ (E a).map φ ≫ (χ.iso f).hom.app N :=
  rfl

/-- **The crossing bijection intertwines the maps attached to a presented factorisation.**  For
`f ≫ g = k` the map `CategoryTheory.PullbackData.factorHom` of `Pm` followed by the bijection at
`k` is the bijection at `g` followed by the map `factorHom` of `P`.

This is the whole content of `CategoryTheory.PullbackData.Crossing.iso_triangle`, read on
morphism sets, and it is what the transition maps and the maps to the vertex of the system of
Stacks 09RI are. -/
theorem homEquiv_factorHom {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k)
    (M N : Dm c) (φ : (Pm.pull g).obj M ⟶ (Pm.pull g).obj N) :
    χ.homEquiv hE k M N (Pm.factorHom hk φ) = P.factorHom hk (χ.homEquiv hE g M N φ) := by
  have hM : (χ.iso k).hom.app M ≫ (P.triangle hk).hom.app ((E c).obj M) ≫
        (P.pull f).map ((χ.iso g).inv.app M) =
      (E a).map ((Pm.triangle hk).hom.app M) ≫ (χ.iso f).hom.app ((Pm.pull g).obj M) := by
    rw [← reassoc_of% (χ.iso_triangle hk M), ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hN : (χ.iso f).hom.app ((Pm.pull g).obj N) ≫ (P.pull f).map ((χ.iso g).hom.app N) =
      (E a).map ((Pm.triangle hk).inv.app N) ≫ (χ.iso k).hom.app N ≫
        (P.triangle hk).hom.app ((E c).obj N) := by
    rw [← χ.iso_triangle hk N, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  have hnat := (χ.iso f).hom.naturality φ
  simp only [Functor.comp_map] at hnat
  have key : (χ.iso k).hom.app M ≫ P.factorHom hk (χ.homEquiv hE g M N φ) =
      (E a).map (Pm.factorHom hk φ) ≫ (χ.iso k).hom.app N := by
    simp only [homEquiv_apply, factorHom, Functor.conjHom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hM, ← reassoc_of% hnat, reassoc_of% hN]
    simp only [Iso.hom_inv_id_app, Category.comp_id]
  rw [homEquiv_apply, ← key, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

variable {b : A} {J : Type w} [Preorder J] (S : LimitSystem (A := A) b J) (Xm Ym : Dm b)

/-- The colimit statements for `Pm` at `Xm`, `Ym` and for `P` at their images under `E` are
equivalent, via the bijections of `CategoryTheory.PullbackData.Crossing.homEquiv`. -/
private theorem isColim_iff_aux (χ : Crossing Pm P E) (hE : ∀ a : A, (E a).FullyFaithful) :
    S.IsColim Pm Xm Ym ↔ S.IsColim P ((E b).obj Xm) ((E b).obj Ym) := by
  refine ⟨LimitSystem.isColim_of_equiv S Xm Ym _ _ (fun j => χ.homEquiv hE (S.toBase j) Xm Ym)
    (χ.homEquiv hE S.limitToBase Xm Ym) ?_ ?_, Stacks.IsStagesColimit.ofEquiv _ _
    (fun j => χ.homEquiv hE (S.toBase j) Xm Ym) (χ.homEquiv hE S.limitToBase Xm Ym) ?_ ?_⟩
  all_goals first
    | exact fun _ _ hij s => χ.homEquiv_factorHom hE (S.transition_toBase hij) Xm Ym s
    | exact fun j s => χ.homEquiv_factorHom hE (S.proj_toBase j) Xm Ym s

include χ hE in
/-- **The colimit statement of Stacks 09RI transports along a crossing.**  If the morphism group
at the vertex is the filtered colimit of those at the stages for `Pm` at `Xm`, `Ym`, then it is
for `P` at their images under `E`. -/
theorem isColim (h : S.IsColim Pm Xm Ym) :
    S.IsColim P ((E b).obj Xm) ((E b).obj Ym) :=
  (isColim_iff_aux S Xm Ym χ hE).1 h

include χ hE in
/-- **The colimit statement of Stacks 09RI for `Pm` at `Xm`, `Ym` is the colimit statement for
`P` at their images under `E`.**  The converse direction of
`CategoryTheory.PullbackData.Crossing.isColim`, by the same bijections read the other way. -/
theorem isColim_iff :
    S.IsColim Pm Xm Ym ↔ S.IsColim P ((E b).obj Xm) ((E b).obj Ym) :=
  isColim_iff_aux S Xm Ym χ hE

include χ hE in
/-- **The colimit statement at every shift of the first argument transports along a crossing.**
The statement for `Pm` at `Xm`, `Ym` gives the statement for `P` at the images under `E` of `Ym`
and of the shifts of `Xm`, and the identifications `hs` of those with the shifts of the image of
`Xm` carry it to the latter — the statement depends on its first argument only up to
isomorphism. -/
theorem shiftedIsColim [∀ a, HasShift (D a) ℤ] [∀ a, HasShift (Dm a) ℤ] [IsDirected J (· ≤ ·)]
    (hP : P.IsCoherent) (hs : ∀ n : ℤ, (E b).obj (Xm⟦n⟧) ≅ ((E b).obj Xm)⟦n⟧)
    (h : LimitSystem.ShiftedIsColim S Pm Xm Ym) :
    LimitSystem.ShiftedIsColim S P ((E b).obj Xm) ((E b).obj Ym) :=
  fun n => (χ.isColim hE S (Xm⟦n⟧) Ym (h n)).of_iso_fst hP (hs n)

end Crossing

end CategoryTheory.PullbackData

end
