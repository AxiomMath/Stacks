/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Shtukas (Drinfeld's F-sheaves) as data

Let `k` be a finite field with `q = p ^ f` elements, `X` a scheme over `k` (in the application,
a smooth projective geometrically irreducible curve) and `S` a scheme over `k`. Write
`X ×_k S` for the fibre product and `τ = id_X × Frob_S` for the endomorphism of `X ×_k S`
given by the `q`-power Frobenius of `S` (it is a morphism over `k`). A *shtuka of rank `r`*
over `S` (Drinfeld's *F-sheaf*, Lafforgue's *chtouca à droite*) consists of

* locally free `𝒪_{X ×_k S}`-modules `E`, `E'` of rank `r`,
* injective maps `j : E ↪ E'` and `t : τ^* E ↪ E'`,
* two morphisms `∞, 0 : S ⟶ X` over `k`, the *pole* and the *zero*,

such that `coker j` is the direct image of an invertible `𝒪_S`-module along the graph
`Γ_∞ : S ⟶ X ×_k S` of the pole, and `coker t` the direct image of an invertible `𝒪_S`-module
along the graph `Γ_0` of the zero. A morphism of shtukas with the same legs is a pair of maps
`E ⟶ F`, `E' ⟶ F'` compatible with `j` and with `t`.

These are the objects whose moduli and `ℓ`-adic cohomology carry, by Drinfeld's theorem, the
Galois representation attached to a cuspidal eigenform on `GL₂` over the function field of `X`
(Stacks Theorem 03VT).

## Main definitions

* `Stacks.Drinfeld.Shtuka.product X S` — the fibre product `X ×_k S`.
* `Stacks.Drinfeld.Shtuka.frobeniusTwist` — `τ = id_X × Frob_S`.
* `Stacks.Drinfeld.Shtuka.partialFrobenius` — `Frob_X × id_S`.
* `Stacks.Drinfeld.Shtuka.productMap` — the base change map `id_X × g`.
* `Stacks.Drinfeld.Shtuka.graph` — the graph `Γ_x : S ⟶ X ×_k S` of a morphism `x : S ⟶ X`.
* `Stacks.Drinfeld.Shtuka.IsGraphLineBundle` — a module is the direct image of an invertible
  `𝒪_S`-module along a graph.
* `Stacks.Drinfeld.Shtuka` — shtukas of rank `r` over `S`, with their category structure
  (`Stacks.Drinfeld.Shtuka.Hom`).

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.pullback_scheme` — the pullback
  of a finite locally free module of rank `r` along a morphism of schemes has rank `r`.
* `frobeniusTwist_fst`, `frobeniusTwist_snd`, `graph_fst`, `graph_snd`.
* `frobeniusTwist_comp_productMap`, `graph_comp_productMap` — `τ` and the graphs commute with
  the base change `id_X × g : X ×_k S' ⟶ X ×_k S`.
* `Stacks.Drinfeld.Shtuka.frobeniusTwist_comp_partialFrobenius` — `τ` composed with the partial
  Frobenius `Frob_X × id_S` is the `q`-power Frobenius of `X ×_k S`; the two commute
  (`frobeniusTwist_comp_partialFrobenius_comm`).
* `Stacks.Drinfeld.Shtuka.isIso_iff` — a morphism of shtukas is an isomorphism if and only if
  its components `E ⟶ F` and `E' ⟶ F'` are.
* `Stacks.Drinfeld.Shtuka.isFiniteLocallyFreeOfRank_frobeniusTwist` — `τ^* E` is locally free of
  rank `r`.

## References

* V. G. Drinfeld, *Langlands' conjecture for GL(2) over functional fields*, Proc. ICM 1978.
* V. G. Drinfeld, *Cohomology of compactified manifolds of modules of F-sheaves of rank 2*,
  J. Soviet Math. 46 (1989).
* L. Lafforgue, *Chtoucas de Drinfeld et correspondance de Langlands*, Invent. Math. 147 (2002),
  §I.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank

/-- **The pullback of a finite locally free module of rank `r` along a morphism of schemes is
finite locally free of rank `r`.** A local free presentation of `M` pulls back to one of the
pullback, over the preimage cover and with the same basis-indexing types. -/
theorem pullback_scheme {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    IsFiniteLocallyFreeOfRank.{u, u, u} ((Scheme.Modules.pullback g).obj M) r := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨q', hq', e, -, hI⟩ :=
    Stacks.Divisors.local_generators_pullback g.base g.toRingCatSheafHom M q hq
  exact ⟨q', hq', fun i => ⟨(Equiv.cast (hI i)).trans (hr (e i)).some⟩⟩

end AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank

namespace Stacks.Drinfeld

open Stacks.Frobenius

variable {k : Type u} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

namespace Shtuka

variable (X S : Over (Spec (.of k)))

/-- The fibre product `X ×_k S`. -/
abbrev product : Scheme.{u} := pullback X.hom S.hom

/-- The endomorphism `τ = id_X × Frob_S` of `X ×_k S`, where `Frob_S` is the `q`-power
Frobenius of `S`, `q = #k = p ^ f`, a morphism over `k`. -/
def frobeniusTwist : product X S ⟶ product X S :=
  pullback.map X.hom S.hom X.hom S.hom (𝟙 _) (geometricFrobenius S p f hcard).left (𝟙 _)
    (by simp) (by rw [Category.comp_id, Over.w])

/-- `τ` commutes with the first projection of `X ×_k S`. -/
@[reassoc (attr := simp)]
theorem frobeniusTwist_fst :
    frobeniusTwist p f hcard X S ≫ pullback.fst X.hom S.hom = pullback.fst X.hom S.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `τ` followed by the second projection is the second projection followed by `Frob_S`. -/
@[reassoc (attr := simp)]
theorem frobeniusTwist_snd :
    frobeniusTwist p f hcard X S ≫ pullback.snd X.hom S.hom =
      pullback.snd X.hom S.hom ≫ (geometricFrobenius S p f hcard).left :=
  pullback.lift_snd _ _ _

/-- The partial Frobenius `Frob_X × id_S` of `X ×_k S`. -/
def partialFrobenius : product X S ⟶ product X S :=
  pullback.map X.hom S.hom X.hom S.hom (geometricFrobenius X p f hcard).left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Over.w]) (by simp)

/-- The partial Frobenius followed by the first projection is the first projection followed by
`Frob_X`. -/
@[reassoc (attr := simp)]
theorem partialFrobenius_fst :
    partialFrobenius p f hcard X S ≫ pullback.fst X.hom S.hom =
      pullback.fst X.hom S.hom ≫ (geometricFrobenius X p f hcard).left :=
  pullback.lift_fst _ _ _

/-- The partial Frobenius commutes with the second projection of `X ×_k S`. -/
@[reassoc (attr := simp)]
theorem partialFrobenius_snd :
    partialFrobenius p f hcard X S ≫ pullback.snd X.hom S.hom = pullback.snd X.hom S.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `X ×_k S` is a scheme over `k`, through the first projection. -/
abbrev productOver : Over (Spec (.of k)) := Over.mk (pullback.fst X.hom S.hom ≫ X.hom)

/-- **The two partial Frobenii commute.** -/
theorem frobeniusTwist_comp_partialFrobenius_comm :
    frobeniusTwist p f hcard X S ≫ partialFrobenius p f hcard X S =
      partialFrobenius p f hcard X S ≫ frobeniusTwist p f hcard X S := by
  apply pullback.hom_ext
  · simp only [Category.assoc, partialFrobenius_fst, frobeniusTwist_fst, frobeniusTwist_fst_assoc]
  · simp only [Category.assoc, partialFrobenius_snd, frobeniusTwist_snd,
      partialFrobenius_snd_assoc]

/-- **`τ` is a partial Frobenius.** The `q`-power absolute Frobenius of `X ×_k S` is the
composite of `τ = id_X × Frob_S` and of the partial Frobenius `Frob_X × id_S`. -/
theorem frobeniusTwist_comp_partialFrobenius :
    frobeniusTwist p f hcard X S ≫ partialFrobenius p f hcard X S =
      (geometricFrobenius (productOver X S) p f hcard).left := by
  have hP : IsInCharacteristic (product X S) p := isInCharacteristic_of_over (productOver X S)
  apply pullback.hom_ext
  · rw [Category.assoc, partialFrobenius_fst, frobeniusTwist_fst_assoc]
    exact (absoluteFrobeniusPow_naturality (pullback.fst X.hom S.hom) p hP
      (isInCharacteristic_of_over X) f).symm
  · rw [Category.assoc, partialFrobenius_snd, frobeniusTwist_snd]
    exact (absoluteFrobeniusPow_naturality (pullback.snd X.hom S.hom) p hP
      (isInCharacteristic_of_over S) f).symm

variable {X S}

/-- The graph `Γ_x = (x, id) : S ⟶ X ×_k S` of a morphism `x : S ⟶ X` over `k`. -/
def graph (x : S ⟶ X) : S.left ⟶ product X S :=
  pullback.lift x.left (𝟙 _) (by rw [Category.id_comp, Over.w])

omit [Fintype k] in
/-- The first component of the graph `Γ_x` is `x`. -/
@[reassoc (attr := simp)]
theorem graph_fst (x : S ⟶ X) : graph x ≫ pullback.fst X.hom S.hom = x.left :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
/-- The second component of the graph `Γ_x` is the identity of `S`. -/
@[reassoc (attr := simp)]
theorem graph_snd (x : S ⟶ X) : graph x ≫ pullback.snd X.hom S.hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The base change map `id_X × g : X ×_k S' ⟶ X ×_k S` of a morphism `g : S' ⟶ S` over `k`. -/
def productMap {S' : Over (Spec (.of k))} (g : S' ⟶ S) : product X S' ⟶ product X S :=
  pullback.map X.hom S'.hom X.hom S.hom (𝟙 _) g.left (𝟙 _) (by simp)
    (by rw [Category.comp_id, Over.w])

omit [Fintype k] in
/-- `id_X × g` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem productMap_fst {S' : Over (Spec (.of k))} (g : S' ⟶ S) :
    productMap g ≫ pullback.fst X.hom S.hom = pullback.fst X.hom S'.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [Fintype k] in
/-- `id_X × g` followed by the second projection is the second projection followed by `g`. -/
@[reassoc (attr := simp)]
theorem productMap_snd {S' : Over (Spec (.of k))} (g : S' ⟶ S) :
    productMap g ≫ pullback.snd X.hom S.hom = pullback.snd X.hom S'.hom ≫ g.left :=
  pullback.lift_snd _ _ _

/-- **`τ` commutes with base change**: `τ_{S'} ≫ (id_X × g) = (id_X × g) ≫ τ_S`, because the
`q`-power Frobenius is natural. -/
theorem frobeniusTwist_comp_productMap {S' : Over (Spec (.of k))} (g : S' ⟶ S) :
    frobeniusTwist p f hcard X S' ≫ productMap g = productMap g ≫ frobeniusTwist p f hcard X S := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productMap_fst, frobeniusTwist_fst]
  · rw [Category.assoc, productMap_snd, frobeniusTwist_snd_assoc, Category.assoc,
      frobeniusTwist_snd, productMap_snd_assoc]
    congr 1
    exact absoluteFrobeniusPow_naturality g.left p (isInCharacteristic_of_over S')
      (isInCharacteristic_of_over S) f

omit [Fintype k] in
/-- The graph of `g ≫ x` maps to the graph of `x` under base change:
`Γ_{x ∘ g} ≫ (id_X × g) = g ≫ Γ_x`. -/
@[reassoc]
theorem graph_comp_productMap {S' : Over (Spec (.of k))} (g : S' ⟶ S) (x : S ⟶ X) :
    graph (g ≫ x) ≫ productMap g = g.left ≫ graph x := by
  apply pullback.hom_ext
  · rw [Category.assoc, productMap_fst, graph_fst, Category.assoc, graph_fst, Over.comp_left]
  · rw [Category.assoc, productMap_snd, graph_snd_assoc, Category.assoc, graph_snd,
      Category.comp_id]

/-- A module `Q` on `X ×_k S` is the direct image `Γ_{x,*} L` of an invertible `𝒪_S`-module `L`
along the graph of `x : S ⟶ X`. -/
def IsGraphLineBundle (Q : (product X S).Modules) (x : S ⟶ X) : Prop :=
  ∃ L : S.left.Modules, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 ∧
    Nonempty (Q ≅ (Scheme.Modules.pushforward (graph x)).obj L)

omit [Fintype k] in
/-- Being the direct image of an invertible module along the graph of `x` is invariant under
isomorphism. -/
theorem IsGraphLineBundle.of_iso {Q Q' : (product X S).Modules} (e : Q ≅ Q') {x : S ⟶ X}
    (h : IsGraphLineBundle Q x) : IsGraphLineBundle Q' x := by
  obtain ⟨L, hL, ⟨e'⟩⟩ := h
  exact ⟨L, hL, ⟨e.symm ≪≫ e'⟩⟩

end Shtuka

/-- A **shtuka of rank `r`** over a scheme `S` over `k` with coefficients in `X` (Drinfeld's
F-sheaf; Lafforgue's *chtouca à droite*): locally free modules `E`, `E'` of rank `r` on
`X ×_k S`, injections `j : E ↪ E'` and `t : τ^* E ↪ E'` (`τ = id_X × Frob_S`), and morphisms
`pole, zero : S ⟶ X` over `k` such that `coker j` is the direct image of an invertible
`𝒪_S`-module along the graph of the pole and `coker t` the direct image of an invertible
`𝒪_S`-module along the graph of the zero. -/
structure Shtuka (X S : Over (Spec (.of k))) (r : ℕ) where
  /-- The locally free module `E`. -/
  E : (Shtuka.product X S).Modules
  /-- The locally free module `E'`, the target of both modifications. -/
  E' : (Shtuka.product X S).Modules
  isFiniteLocallyFreeOfRank_E : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r
  isFiniteLocallyFreeOfRank_E' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r
  /-- The modification `j : E ↪ E'`, an isomorphism away from the graph of the pole. -/
  j : E ⟶ E'
  /-- The modification `t : τ^* E ↪ E'`, an isomorphism away from the graph of the zero. -/
  t : (Scheme.Modules.pullback (Shtuka.frobeniusTwist p f hcard X S)).obj E ⟶ E'
  mono_j : Mono j
  mono_t : Mono t
  /-- The pole `∞ : S ⟶ X`. -/
  pole : S ⟶ X
  /-- The zero `0 : S ⟶ X`. -/
  zero : S ⟶ X
  isGraphLineBundle_cokernel_j : Shtuka.IsGraphLineBundle (cokernel j) pole
  isGraphLineBundle_cokernel_t : Shtuka.IsGraphLineBundle (cokernel t) zero

namespace Shtuka

variable {p f hcard} {X S : Over (Spec (.of k))} {r : ℕ}

/-- `τ^* E` is locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_frobeniusTwist (𝓔 : Shtuka p f hcard X S r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (frobeniusTwist p f hcard X S)).obj 𝓔.E) r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.pullback_scheme _ _ r 𝓔.isFiniteLocallyFreeOfRank_E

/-- A morphism of shtukas with the same pole and zero: maps `E ⟶ F` and `E' ⟶ F'` commuting with
the modifications `j` and `t`. -/
@[ext]
structure Hom (𝓔 𝓕 : Shtuka p f hcard X S r) where
  /-- The map `E ⟶ F`. -/
  hom : 𝓔.E ⟶ 𝓕.E
  /-- The map `E' ⟶ F'`. -/
  hom' : 𝓔.E' ⟶ 𝓕.E'
  pole_eq : 𝓔.pole = 𝓕.pole
  zero_eq : 𝓔.zero = 𝓕.zero
  j_comp : 𝓔.j ≫ hom' = hom ≫ 𝓕.j
  t_comp : 𝓔.t ≫ hom' =
    (Scheme.Modules.pullback (frobeniusTwist p f hcard X S)).map hom ≫ 𝓕.t

attribute [reassoc] Hom.j_comp Hom.t_comp

/-- Shtukas of rank `r` over `S`, with their morphisms of fixed pole and zero, form a category. -/
instance : Category (Shtuka p f hcard X S r) where
  Hom := Hom
  id 𝓔 :=
    { hom := 𝟙 _
      hom' := 𝟙 _
      pole_eq := rfl
      zero_eq := rfl
      j_comp := by simp
      t_comp := by simp }
  comp α β :=
    { hom := α.hom ≫ β.hom
      hom' := α.hom' ≫ β.hom'
      pole_eq := α.pole_eq.trans β.pole_eq
      zero_eq := α.zero_eq.trans β.zero_eq
      j_comp := by rw [α.j_comp_assoc, β.j_comp, Category.assoc]
      t_comp := by rw [α.t_comp_assoc, β.t_comp, Functor.map_comp, Category.assoc] }

/-- Two morphisms of shtukas agreeing on `E` and on `E'` are equal. -/
@[ext]
theorem hom_ext {𝓔 𝓕 : Shtuka p f hcard X S r} {α β : 𝓔 ⟶ 𝓕} (h : α.hom = β.hom)
    (h' : α.hom' = β.hom') : α = β :=
  Hom.ext h h'

/-- The identity morphism of a shtuka is the identity on `E`. -/
@[simp] theorem id_hom (𝓔 : Shtuka p f hcard X S r) : (𝟙 𝓔 : 𝓔 ⟶ 𝓔).hom = 𝟙 _ := rfl

/-- The identity morphism of a shtuka is the identity on `E'`. -/
@[simp] theorem id_hom' (𝓔 : Shtuka p f hcard X S r) : (𝟙 𝓔 : 𝓔 ⟶ 𝓔).hom' = 𝟙 _ := rfl

/-- The map on `E` of a composite of morphisms of shtukas is the composite of the maps. -/
@[simp, reassoc] theorem comp_hom {𝓔 𝓕 𝓖 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) (β : 𝓕 ⟶ 𝓖) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

/-- The map on `E'` of a composite of morphisms of shtukas is the composite of the maps. -/
@[simp, reassoc] theorem comp_hom' {𝓔 𝓕 𝓖 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) (β : 𝓕 ⟶ 𝓖) :
    (α ≫ β).hom' = α.hom' ≫ β.hom' := rfl

variable (p f hcard X S r) in
/-- The functor `𝓔 ↦ E` from shtukas to modules on `X ×_k S`. -/
@[simps]
def forget : Shtuka p f hcard X S r ⥤ (product X S).Modules where
  obj 𝓔 := 𝓔.E
  map α := α.hom

variable (p f hcard X S r) in
/-- The functor `𝓔 ↦ E'` from shtukas to modules on `X ×_k S`. -/
@[simps]
def forget' : Shtuka p f hcard X S r ⥤ (product X S).Modules where
  obj 𝓔 := 𝓔.E'
  map α := α.hom'

/-- Inverting the two isomorphisms of a commutative square gives a commutative square. -/
private theorem inv_comp_comm {C : Type*} [Category C] {A B A' B' : C} {u : A ⟶ B} {a : A ⟶ A'}
    {b : B ⟶ B'} {v : A' ⟶ B'} [IsIso a] [IsIso b] (h : u ≫ b = a ≫ v) :
    v ≫ inv b = inv a ≫ u := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- A morphism of shtukas whose two components are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso {𝓔 𝓕 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) [IsIso α.hom]
    [IsIso α.hom'] : IsIso α := by
  let β : 𝓕 ⟶ 𝓔 :=
    { hom := inv α.hom
      hom' := inv α.hom'
      pole_eq := α.pole_eq.symm
      zero_eq := α.zero_eq.symm
      j_comp := inv_comp_comm α.j_comp
      t_comp := by rw [Functor.map_inv]; exact inv_comp_comm α.t_comp }
  exact ⟨β, hom_ext (IsIso.hom_inv_id α.hom) (IsIso.hom_inv_id α.hom'),
    hom_ext (IsIso.inv_hom_id α.hom) (IsIso.inv_hom_id α.hom')⟩

/-- **Isomorphisms of shtukas.** A morphism of shtukas is an isomorphism if and only if both of
its components `E ⟶ F` and `E' ⟶ F'` are isomorphisms. -/
theorem isIso_iff {𝓔 𝓕 : Shtuka p f hcard X S r} (α : 𝓔 ⟶ 𝓕) :
    IsIso α ↔ IsIso α.hom ∧ IsIso α.hom' := by
  refine ⟨fun _ => ⟨(inferInstance : IsIso ((forget p f hcard X S r).map α)),
    (inferInstance : IsIso ((forget' p f hcard X S r).map α))⟩, fun ⟨_, _⟩ => isIso_of_isIso α⟩

end Shtuka

end Stacks.Drinfeld
