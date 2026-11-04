module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineLimitGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of a quasi-coherent module on a limit of algebraic spaces

Let `X = lim Xᵢ` be the limit in a limit situation over `S` (Situation 084R,
`AlgebraicGeometry.Space.LimitSituation`): a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms, its limit `X`, and a
chosen index `0`. For a module `ℱ₀` on `X₀` set `ℱᵢ = f_{0i}^*ℱ₀` for `i ≥ 0` and
`ℱ = f_0^*ℱ₀`. Stacks 07SI asserts that `Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)` when `ℱ₀` is
quasi-coherent.

This file states that assertion, shows that a system of equalizers has the equalizer of the
colimits as its colimit, and proves the structure-sheaf case of Stacks 01Z0, so that the
assertion follows from equalizer presentations of the groups of global sections.

## Main definitions

* `Stacks.IsStagesColimit` is the elementwise form of "`T` is the filtered colimit of the stages
  `G i` along `ι`": the maps to `T` are compatible with the transition maps, every element of `T`
  comes from a stage, and two elements of a stage with the same image in `T` already agree at
  some later stage. For a directed index set these three conditions are exactly the assertion
  that `T = colim G i`.
* `AlgebraicGeometry.Space.modulePullbackSections` is the inverse image of a global section of an
  `𝒪`-module along a morphism of algebraic spaces: a global section is a morphism out of the
  structure sheaf (`SheafOfModules.unitHomEquiv`), and its inverse image is the inverse image of
  that morphism read through `AlgebraicGeometry.Space.modulePullbackUnitIso`.
* `AlgebraicGeometry.Space.LimitSituation.stage`,
  `AlgebraicGeometry.Space.LimitSituation.limitSpace`,
  `AlgebraicGeometry.Space.LimitSituation.transition` and
  `AlgebraicGeometry.Space.LimitSituation.projection` read a limit situation in the category of
  algebraic spaces over the base.
* `AlgebraicGeometry.Space.LimitSituation.stageModule` and
  `AlgebraicGeometry.Space.LimitSituation.limitModule` are the modules `ℱᵢ = f_{0i}^*ℱ₀` and
  `ℱ = f_0^*ℱ₀`, with
  `AlgebraicGeometry.Space.LimitSituation.stageTransition` and
  `AlgebraicGeometry.Space.LimitSituation.stageProjection` the induced maps
  `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` and `Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)`.
* `AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` is the assertion of Stacks 07SI:
  that those data exhibit `Γ(X, ℱ)` as the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`.

## Main results

* `Stacks.IsStagesColimit.equalizer`: if `A'` is the filtered colimit of the `A i` and `B'` of
  the `B i`, and `p, q : A ⟶ B` is a pair of parallel maps compatible with the transition maps
  and with the maps to the colimits, then the stagewise equalizer of `p` and `q` has the
  equalizer of `p'` and `q'` as its filtered colimit.
* `Stacks.IsStagesColimit.ofEquiv`: a colimit assertion transports along stagewise bijections
  compatible with the transition maps and the maps to the vertex.
* `AlgebraicGeometry.Space.LimitSituation.transition_comp` and
  `AlgebraicGeometry.Space.LimitSituation.projection_comp_transition`: the composition laws for
  the transition morphisms and the projections of a limit situation, read in the category of
  algebraic spaces.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equiv`: the assertion of
  Stacks 07SI follows from a colimit assertion for any system of types stagewise identified with
  the groups of global sections.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation`: given
  equalizer presentations of the groups of global sections at the stages and at the limit, over
  two systems whose colimit assertions are hypotheses, the assertion of Stacks 07SI holds.
* `AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`: for an inverse
  system of *affine* schemes over a directed preorder, the ring of global sections of the limit
  is the filtered colimit of the rings of global sections of the stages, in the elementwise form
  `Stacks.IsStagesColimit`.
* `AlgebraicGeometry.isStagesColimit_appTop_of_isLimit_of_directed`: the same statement for an
  inverse system of *quasi-compact and quasi-separated* schemes with affine transition
  morphisms.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`:
  when the chart system and the relation system are both systems of *affine* schemes, equalizer
  presentations in their rings of global sections imply the assertion of Stacks 07SI.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_qcqs`:
  the same with the relation system only quasi-compact and quasi-separated, with affine
  transition morphisms.

## Implementation notes

The colimit assertion is stated by its three elementwise clauses rather than as
`CategoryTheory.Limits.IsColimit` of a cocone of abelian groups: the maps
`Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` are built from the inverse-image comparison
`AlgebraicGeometry.Space.modulePullbackCompIso`, which composes only up to a canonical
isomorphism, so the stages do not form a strict diagram without extra coherence. For a directed
index set the three clauses are exactly the assertion `Γ(X, ℱ) = colim Γ(Xᵢ, ℱᵢ)`.
`Stacks.IsStagesColimit.equalizer` and `Stacks.IsStagesColimit.ofEquiv` hold over any preorder.

The index set of `AlgebraicGeometry.Space.LimitSituation` lies in the universe of the site. Over
an index set one universe up the scheme-level assertion of Stacks 01Z0 is false
(`Stacks.LimitSectionsIdentification.not_card_01Z0`).

`AlgebraicGeometry.Space.LimitSituation` records `X` only as a limiting cone of presheaves; that
the limit is an algebraic space is Stacks 07SF and needs the size hypotheses of that tag, so it
appears below as an explicit hypothesis `hX`.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ w₄ v u

namespace Stacks

/-! ### Filtered colimits of a system of stages, elementwise -/

/-- **The elementwise form of "`T` is the filtered colimit of the stages `G i`".** The index is
any preorder; `trans` are the transition maps of the system and `ι` the maps to `T`.

For a directed index set the three clauses are exactly the assertion that `T` is the colimit of
the system: the maps to `T` form a cocone, the cocone is jointly surjective, and two elements of
one stage with the same image in `T` become equal at some later stage. -/
structure IsStagesColimit {I : Type v} [Preorder I] {G : I → Type w₁} {T : Type w₂}
    (trans : ∀ i j : I, i ≤ j → G i → G j) (ι : ∀ i : I, G i → T) : Prop where
  /-- The maps to `T` are compatible with the transition maps. -/
  ι_trans : ∀ (i j : I) (h : i ≤ j) (s : G i), ι j (trans i j h s) = ι i s
  /-- Every element of `T` comes from some stage. -/
  exists_stage : ∀ t : T, ∃ (i : I) (s : G i), ι i s = t
  /-- Two elements of one stage with the same image in `T` agree at some later stage. -/
  exists_trans_eq : ∀ (i : I) (s s' : G i), ι i s = ι i s' →
    ∃ (j : I) (h : i ≤ j), trans i j h s = trans i j h s'

/-! ### The ring-theoretic reading of a colimit assertion -/

section Ring

variable {ι : Type v} [Preorder ι] {G : ι → Type w₁} [∀ i, CommRing (G i)]
  {A : Type w₂} [CommRing A] {f : ∀ i j, i ≤ j → G i →+* G j} {φ : ∀ i, G i →+* A}

/-- For a colimit assertion of rings, the maps to the vertex are compatible with the transition
maps. -/
theorem IsStagesColimit.hφ
    (h : IsStagesColimit (fun i j hij x => f i j hij x) (fun i x => φ i x))
    (i j : ι) (hij : i ≤ j) (x : G i) : φ j (f i j hij x) = φ i x :=
  h.ι_trans i j hij x

/-- For a colimit assertion of rings, every element of the vertex comes from a stage. -/
theorem IsStagesColimit.hsurj
    (h : IsStagesColimit (fun i j hij x => f i j hij x) (fun i x => φ i x))
    (a : A) : ∃ (i : ι) (x : G i), φ i x = a :=
  h.exists_stage a

/-- For a colimit assertion of rings, an element of a stage that dies in the colimit already
dies at a later stage. -/
theorem IsStagesColimit.hzero
    (h : IsStagesColimit (fun i j hij x => f i j hij x) (fun i x => φ i x))
    (i : ι) (x : G i) (hx : φ i x = 0) : ∃ (j : ι) (hij : i ≤ j), f i j hij x = 0 := by
  obtain ⟨j, hij, hj⟩ := h.exists_trans_eq i x 0 (by rw [hx, map_zero])
  exact ⟨j, hij, by simpa only [map_zero] using hj⟩

/-- **A colimit assertion for a system of rings, in ring-theoretic form.** For ring
homomorphisms `f` and `φ`, `Stacks.IsStagesColimit` holds exactly when the maps `φ` are
compatible with the `f`, every element of `A` comes from a stage, and an element of a stage
whose image in `A` vanishes already vanishes at a later stage. -/
theorem isStagesColimit_iff_ring :
    IsStagesColimit (fun i j hij x => f i j hij x) (fun i x => φ i x) ↔
      ((∀ (i j : ι) (hij : i ≤ j) (x : G i), φ j (f i j hij x) = φ i x) ∧
        (∀ a : A, ∃ (i : ι) (x : G i), φ i x = a) ∧
        ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (hij : i ≤ j), f i j hij x = 0) := by
  refine ⟨fun h => ⟨h.hφ, h.hsurj, h.hzero⟩, fun ⟨hφ, hsurj, hzero⟩ => ⟨hφ, hsurj, ?_⟩⟩
  intro i x y hxy
  obtain ⟨j, hij, hj⟩ := hzero i (x - y) (by rw [map_sub, hxy, sub_self])
  exact ⟨j, hij, sub_eq_zero.mp ((map_sub _ x y).symm.trans hj)⟩

end Ring

/-- **A directed system of equalizers has the equalizer of the colimits as its colimit.** Let
`p, q : A ⟶ B` be two parallel families of maps between systems of stages, compatible with the
transition maps and with the maps to `A'` and `B'`, and suppose `A'` is the filtered colimit of
the `A i` and `B'` is the filtered colimit of the `B i`. Then the stagewise equalizer
`{a : A i // p i a = q i a}` has `{a : A' // p' a = q' a}` as its filtered colimit. -/
theorem IsStagesColimit.equalizer {I : Type v} [Preorder I]
    {A : I → Type w₁} {A' : Type w₂} {Bs : I → Type w₃} {B' : Type w₄}
    {transA : ∀ i j : I, i ≤ j → A i → A j} {ιA : ∀ i : I, A i → A'}
    {transB : ∀ i j : I, i ≤ j → Bs i → Bs j} {ιB : ∀ i : I, Bs i → B'}
    {p q : ∀ i : I, A i → Bs i} {p' q' : A' → B'}
    (hpt : ∀ (i j : I) (h : i ≤ j) (a : A i), p j (transA i j h a) = transB i j h (p i a))
    (hqt : ∀ (i j : I) (h : i ≤ j) (a : A i), q j (transA i j h a) = transB i j h (q i a))
    (hpi : ∀ (i : I) (a : A i), p' (ιA i a) = ιB i (p i a))
    (hqi : ∀ (i : I) (a : A i), q' (ιA i a) = ιB i (q i a))
    (hA : IsStagesColimit transA ιA) (hB : IsStagesColimit transB ιB) :
    IsStagesColimit
      (fun i j h (s : {a : A i // p i a = q i a}) =>
        (⟨transA i j h s.1, by rw [hpt, hqt, s.2]⟩ : {a : A j // p j a = q j a}))
      (fun i (s : {a : A i // p i a = q i a}) =>
        (⟨ιA i s.1, by rw [hpi, hqi, s.2]⟩ : {a : A' // p' a = q' a})) where
  ι_trans i j h s := Subtype.ext (hA.ι_trans i j h s.1)
  exists_stage t := by
    obtain ⟨i, a, ha⟩ := hA.exists_stage t.1
    have hb : ιB i (p i a) = ιB i (q i a) := by
      rw [← hpi, ← hqi, ha]; exact t.2
    obtain ⟨j, hij, hj⟩ := hB.exists_trans_eq i (p i a) (q i a) hb
    refine ⟨j, ⟨transA i j hij a, ?_⟩, Subtype.ext ((hA.ι_trans i j hij a).trans ha)⟩
    rw [hpt, hqt]; exact hj
  exists_trans_eq i s s' hss := by
    obtain ⟨j, hij, hj⟩ := hA.exists_trans_eq i s.1 s'.1 (congrArg Subtype.val hss)
    exact ⟨j, hij, Subtype.ext hj⟩

/-- **A colimit assertion transports along stagewise bijections.** If each stage `G' i` is in
bijection with `G i` and the vertex `T'` with `T`, compatibly with the transition maps and the
maps to the vertex, then `T'` is the filtered colimit of the `G' i` as soon as `T` is the
filtered colimit of the `G i`. -/
theorem IsStagesColimit.ofEquiv {I : Type v} [Preorder I]
    {G : I → Type w₁} {T : Type w₂} {G' : I → Type w₃} {T' : Type w₄}
    {trans : ∀ i j : I, i ≤ j → G i → G j} {ι : ∀ i : I, G i → T}
    (trans' : ∀ i j : I, i ≤ j → G' i → G' j) (ι' : ∀ i : I, G' i → T')
    (e : ∀ i : I, G' i ≃ G i) (eT : T' ≃ T)
    (he : ∀ (i j : I) (h : i ≤ j) (s : G' i), e j (trans' i j h s) = trans i j h (e i s))
    (heT : ∀ (i : I) (s : G' i), eT (ι' i s) = ι i (e i s))
    (hG : IsStagesColimit trans ι) : IsStagesColimit trans' ι' where
  ι_trans i j h s := eT.injective (by simp only [heT, he, hG.ι_trans])
  exists_stage t := by
    obtain ⟨i, s, hs⟩ := hG.exists_stage (eT t)
    exact ⟨i, (e i).symm s,
      eT.injective (by simpa only [heT, Equiv.apply_symm_apply] using hs)⟩
  exists_trans_eq i s s' hss := by
    obtain ⟨j, hij, hj⟩ := hG.exists_trans_eq i (e i s) (e i s')
      (by simp only [← heT]; exact congrArg eT hss)
    exact ⟨j, hij, (e j).injective (by simpa only [he] using hj)⟩

end Stacks

namespace AlgebraicGeometry

/-! ### The affine case of Stacks 01Z0 for the structure sheaf, elementwise -/

section AffineStructureSheaf

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (E : αᵒᵖ ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c) [∀ a, IsAffine (E.obj a)]

include hc in
/-- **The ring of global sections of a limit of affine schemes is the filtered colimit of the
rings of global sections of the stages**, in the elementwise form `Stacks.IsStagesColimit`: the
transition maps are the pullbacks of global sections along the morphisms of the inverse system
and the maps to the vertex are the pullbacks along the projections of the limiting cone. -/
@[stacks 01Z0 "for the structure sheaf over a directed inverse system of affine schemes, with \
the index set in the universe of the schemes",
  ega "IV 8.5.4" "special case",
  sga "3 VIB 10.0" "(i), special case"]
theorem isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed :
    Stacks.IsStagesColimit (G := fun a : α => (Γ(E.obj (op a), ⊤) : Type u))
      (T := (Γ(c.pt, ⊤) : Type u))
      (fun (a b : α) (h : a ≤ b) x => (E.map (homOfLE h).op).appTop.hom x)
      (fun (a : α) x => (c.π.app (op a)).appTop.hom x) :=
  Stacks.isStagesColimit_iff_ring.2
    ⟨fun a b h x => by rw [← elementwise_of% Scheme.Hom.comp_appTop, c.w (homOfLE h).op],
      exists_appTop_eq_of_isAffine_of_isLimit_of_directed E c hc,
      exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed E c hc⟩

end AffineStructureSheaf

/-! ### The quasi-compact quasi-separated case of Stacks 01Z0 for the structure sheaf -/

section QcqsStructureSheaf

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (E : αᵒᵖ ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
  [∀ {a b : αᵒᵖ} (f : a ⟶ b), IsAffineHom (E.map f)]
  [∀ a, CompactSpace (E.obj a)] [∀ a, QuasiSeparatedSpace (E.obj a)]

include hc in
/-- **The ring of global sections of a limit of quasi-compact quasi-separated schemes with
affine transition morphisms is the filtered colimit of the rings of global sections of the
stages**, in the elementwise form `Stacks.IsStagesColimit`: the transition maps are the
pullbacks of global sections along the morphisms of the inverse system and the maps to the
vertex are the pullbacks along the projections of the limiting cone. -/
@[stacks 01Z0 "for the structure sheaf over a directed inverse system of quasi-compact \
quasi-separated schemes with affine transition morphisms, with the index set in the universe \
of the schemes", ega "IV 8.5.4" "structure sheaf"]
theorem isStagesColimit_appTop_of_isLimit_of_directed :
    Stacks.IsStagesColimit (G := fun a : α => (Γ(E.obj (op a), ⊤) : Type u))
      (T := (Γ(c.pt, ⊤) : Type u))
      (fun (a b : α) (h : a ≤ b) x => (E.map (homOfLE h).op).appTop.hom x)
      (fun (a : α) x => (c.π.app (op a)).appTop.hom x) where
  ι_trans a b h x := by
    rw [← elementwise_of% Scheme.Hom.comp_appTop, c.w (homOfLE h).op]
  exists_stage t := by
    obtain ⟨a, s, hs⟩ := exists_appTop_π_eq_of_isLimit E c hc t
    exact ⟨a.unop, s, hs.symm⟩
  exists_trans_eq a x y hxy := by
    obtain ⟨b, g, hg⟩ :=
      exists_app_map_eq_map_of_isLimit E c hc (U := ⊤) isCompact_univ x y hxy
    refine ⟨b.unop, leOfHom g.unop, ?_⟩
    rwa [show (homOfLE (leOfHom g.unop)).op = g from Subsingleton.elim _ _]

end QcqsStructureSheaf

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Inverse image of a global section of a module -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of a global section of an `𝒪`-module along a morphism of algebraic
spaces.** A global section of `M` is a morphism `𝒪_Y ⟶ M` (`SheafOfModules.unitHomEquiv`); its
inverse image is the composite `𝒪_X ≅ f^*𝒪_Y ⟶ f^*M`, where the first map is the inverse of
`AlgebraicGeometry.Space.modulePullbackUnitIso`, read back as a global section of `f^*M`. -/
def modulePullbackSections {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.obj Y.property) (s : M.sections) :
    ((modulePullback B S hS f).obj M).sections :=
  SheafOfModules.unitHomEquiv _
    ((modulePullbackUnitIso B S hS f).inv ≫
      (modulePullback B S hS f).map ((SheafOfModules.unitHomEquiv M).symm s))

/-- **The comparison of an iterated inverse image with the inverse image along a composite**, for
`f ≫ g = k`: the comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU
followed by the identification of the inverse images along `f ≫ g` and `k`. -/
def modulePullbackCompComparison {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (w : f ≫ g = k) (M : Modules.{u, u} B S hS Z.obj Z.property) :
    (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) ⟶
      (modulePullback B S hS k).obj M :=
  (modulePullbackCompIso B S hS f g).hom.app M ≫
    eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M) w)

/-! ### Situation 084R in the category of algebraic spaces -/

namespace LimitSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

/-- The stages of a limit situation at or beyond its chosen index, as a preorder. -/
abbrev Stages := {i : A.I // A.base ≤ i}

/-- The stages of a limit situation at or beyond its chosen index are nonempty. -/
instance : Nonempty A.Stages := ⟨⟨A.base, le_refl _⟩⟩

/-- The stages of a limit situation at or beyond its chosen index are directed. -/
instance : IsDirected A.Stages (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := A.isDirected.directed i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-- The stage `Xᵢ` of a limit situation, as an object of the category of algebraic spaces over
the base. -/
def stage (i : A.I) : AlgebraicSpaces B S hS := ⟨A.system.obj (op i), A.isAlgebraicSpace i⟩

/-- The limit `X` of a limit situation, as an object of the category of algebraic spaces over the
base, given that it is an algebraic space. -/
def limitSpace (hX : IsAlgebraicSpace B S hS X) : AlgebraicSpaces B S hS := ⟨A.cone.pt, hX⟩

/-- The transition morphism `f_{ji} : Xⱼ ⟶ Xᵢ` of a limit situation, for `i ≤ j`, in the category
of algebraic spaces over the base. -/
def transition {i j : A.I} (h : i ≤ j) : A.stage j ⟶ A.stage i :=
  ObjectProperty.homMk (A.system.map (homOfLE h).op)

/-- The projection `fᵢ : X ⟶ Xᵢ` from the limit of a limit situation to one of its stages, in the
category of algebraic spaces over the base. -/
def projection (hX : IsAlgebraicSpace B S hS X) (i : A.I) : A.limitSpace hX ⟶ A.stage i :=
  ObjectProperty.homMk (A.π.app (op i))

/-- **The transition morphisms of a limit situation compose**: `f_{kj} ≫ f_{ji} = f_{ki}` for
`i ≤ j ≤ k`. -/
theorem transition_comp {i j k : A.I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) :
    A.transition hjk ≫ A.transition hij = A.transition hik := by
  apply ObjectProperty.hom_ext
  show A.system.map (homOfLE hjk).op ≫ A.system.map (homOfLE hij).op
      = A.system.map (homOfLE hik).op
  rw [← A.system.map_comp]
  rfl

/-- **A projection of a limit situation followed by a transition morphism is a projection**:
`fⱼ ≫ f_{ji} = fᵢ` for `i ≤ j`. -/
theorem projection_comp_transition (hX : IsAlgebraicSpace B S hS X) {i j : A.I} (h : i ≤ j) :
    A.projection hX j ≫ A.transition h = A.projection hX i := by
  apply ObjectProperty.hom_ext
  show A.π.app (op j) ≫ A.system.map (homOfLE h).op = A.π.app (op i)
  exact A.cone.w (homOfLE h).op

/-! ### The modules and the groups of global sections of Stacks 07SI -/

variable (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **The module `ℱᵢ = f_{0i}^*ℱ₀` of Stacks 07SI**: the inverse image of a module on the chosen
stage to a later stage. -/
def stageModule (i : A.Stages) :
    Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property :=
  (modulePullback B S hS (A.transition i.2)).obj F₀

/-- **The module `ℱ = f_0^*ℱ₀` of Stacks 07SI**: the inverse image to the limit of a module on
the chosen stage. -/
def limitModule (hX : IsAlgebraicSpace B S hS X) :
    Modules.{u, u} B S hS (A.limitSpace hX).obj (A.limitSpace hX).property :=
  (modulePullback B S hS (A.projection hX A.base)).obj F₀

/-- **The group `Γ(Xᵢ, ℱᵢ)` of Stacks 07SI.** -/
abbrev stageSections (i : A.Stages) := (A.stageModule F₀ i).sections

/-- **The group `Γ(X, ℱ)` of Stacks 07SI.** -/
abbrev limitSections (hX : IsAlgebraicSpace B S hS X) := (A.limitModule F₀ hX).sections

/-- **The comparison `f_{ji}^*ℱᵢ ⟶ ℱⱼ`**: the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of the iterated inverse image with the inverse
image along the composite `f_{ji} ≫ f_{0i} = f_{0j}`. -/
def stageTransitionComparison (i j : A.Stages) (h : i ≤ j) :
    (modulePullback B S hS (A.transition h)).obj (A.stageModule F₀ i) ⟶ A.stageModule F₀ j :=
  modulePullbackCompComparison B S hS (A.transition h) (A.transition i.2) (A.transition j.2)
    (A.transition_comp i.2 h j.2) F₀

/-- **The transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` of Stacks 07SI**: the inverse image of a global
section along `f_{ji}`, read through the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of the iterated inverse image with the inverse
image along the composite `f_{ji} ≫ f_{0i} = f_{0j}`. -/
def stageTransition (i j : A.Stages) (h : i ≤ j) :
    A.stageSections F₀ i → A.stageSections F₀ j := fun s =>
  SheafOfModules.sectionsMap (A.stageTransitionComparison F₀ i j h)
    (modulePullbackSections B S hS (A.transition h) (A.stageModule F₀ i) s)

/-- The transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)`, unfolded. -/
theorem stageTransition_eq (i j : A.Stages) (h : i ≤ j) (s : A.stageSections F₀ i) :
    A.stageTransition F₀ i j h s
      = SheafOfModules.sectionsMap (A.stageTransitionComparison F₀ i j h)
        (modulePullbackSections B S hS (A.transition h) (A.stageModule F₀ i) s) :=
  rfl

/-- **The comparison `fᵢ^*ℱᵢ ⟶ ℱ`**: the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of the iterated inverse image with the inverse
image along the composite `fᵢ ≫ f_{0i} = f_0`. -/
def stageProjectionComparison (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    (modulePullback B S hS (A.projection hX i.1)).obj (A.stageModule F₀ i) ⟶
      A.limitModule F₀ hX :=
  modulePullbackCompComparison B S hS (A.projection hX i.1) (A.transition i.2)
    (A.projection hX A.base) (A.projection_comp_transition hX i.2) F₀

/-- **The map `Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)` of Stacks 07SI**: the inverse image of a global section along
the projection `fᵢ`, read through the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of the iterated inverse image with the inverse
image along the composite `fᵢ ≫ f_{0i} = f_0`. -/
def stageProjection (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    A.stageSections F₀ i → A.limitSections F₀ hX := fun s =>
  SheafOfModules.sectionsMap (A.stageProjectionComparison F₀ hX i)
    (modulePullbackSections B S hS (A.projection hX i.1) (A.stageModule F₀ i) s)

/-- The map `Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)`, unfolded. -/
theorem stageProjection_eq (hX : IsAlgebraicSpace B S hS X) (i : A.Stages)
    (s : A.stageSections F₀ i) :
    A.stageProjection F₀ hX i s
      = SheafOfModules.sectionsMap (A.stageProjectionComparison F₀ hX i)
        (modulePullbackSections B S hS (A.projection hX i.1) (A.stageModule F₀ i) s) :=
  rfl

/-- **The assertion of Stacks 07SI**: in Situation 084R, the global sections of the inverse image
to the limit of a module on the chosen stage are the filtered colimit, over the stages at or
beyond the chosen one, of the global sections of its inverse images to those stages — along the
maps `AlgebraicGeometry.Space.LimitSituation.stageTransition` and
`AlgebraicGeometry.Space.LimitSituation.stageProjection`, taken elementwise as
`Stacks.IsStagesColimit`.

Stacks 07SI asserts this for a *quasi-coherent* `ℱ₀`; quasi-coherence is a hypothesis of the tag
and not part of this assertion, which is stated for every module and is false in general. -/
def IsSectionsColimit (hX : IsAlgebraicSpace B S hS X) : Prop :=
  Stacks.IsStagesColimit (A.stageTransition F₀) (A.stageProjection F₀ hX)

/-- **The assertion of Stacks 07SI follows from a colimit assertion for any stagewise model of
its groups of global sections.** If a system of types `G` with vertex `T` is a filtered colimit
and is identified stagewise with the groups `Γ(Xᵢ, ℱᵢ)` and `Γ(X, ℱ)`, compatibly with the
transition maps and the maps to the limit, then `Γ(X, ℱ)` is the filtered colimit of the
`Γ(Xᵢ, ℱᵢ)`. -/
theorem isSectionsColimit_of_equiv (hX : IsAlgebraicSpace B S hS X)
    {G : A.Stages → Type w₁} {T : Type w₂}
    (trans : ∀ i j : A.Stages, i ≤ j → G i → G j) (ι : ∀ i : A.Stages, G i → T)
    (e : ∀ i : A.Stages, A.stageSections F₀ i ≃ G i) (eT : A.limitSections F₀ hX ≃ T)
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (s : A.stageSections F₀ i),
      e j (A.stageTransition F₀ i j h s) = trans i j h (e i s))
    (heT : ∀ (i : A.Stages) (s : A.stageSections F₀ i),
      eT (A.stageProjection F₀ hX i s) = ι i (e i s))
    (hG : Stacks.IsStagesColimit trans ι) : A.IsSectionsColimit F₀ hX :=
  Stacks.IsStagesColimit.ofEquiv _ _ e eT he heT hG

/-- **The assertion of Stacks 07SI follows from equalizer presentations of its groups of global
sections over two systems that are filtered colimits.** Let `p, q` be two parallel families of
maps from a system `CU` of types to a system `CR`, compatible with the transition maps and with
the maps to the vertices `CU'` and `CR'`, and suppose `CU'` is the filtered colimit of the `CU i`
and `CR'` of the `CR i`. If `Γ(Xᵢ, ℱᵢ)` is in bijection with the equalizer of `p i` and `q i`,
and `Γ(X, ℱ)` with the equalizer of `p'` and `q'`, compatibly with the transition maps and the
maps to the limit, then `Γ(X, ℱ)` is the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`. -/
theorem isSectionsColimit_of_equalizerPresentation (hX : IsAlgebraicSpace B S hS X)
    {CU : A.Stages → Type w₁} {CU' : Type w₂} {CR : A.Stages → Type w₃} {CR' : Type w₄}
    {transU : ∀ i j : A.Stages, i ≤ j → CU i → CU j} {ιU : ∀ i : A.Stages, CU i → CU'}
    {transR : ∀ i j : A.Stages, i ≤ j → CR i → CR j} {ιR : ∀ i : A.Stages, CR i → CR'}
    {p q : ∀ i : A.Stages, CU i → CR i} {p' q' : CU' → CR'}
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (x : CU i),
      p j (transU i j h x) = transR i j h (p i x))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (x : CU i),
      q j (transU i j h x) = transR i j h (q i x))
    (hpi : ∀ (i : A.Stages) (x : CU i), p' (ιU i x) = ιR i (p i x))
    (hqi : ∀ (i : A.Stages) (x : CU i), q' (ιU i x) = ιR i (q i x))
    (e : ∀ i : A.Stages, A.stageSections F₀ i ≃ {x : CU i // p i x = q i x})
    (eT : A.limitSections F₀ hX ≃ {x : CU' // p' x = q' x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (s : A.stageSections F₀ i),
      (e j (A.stageTransition F₀ i j h s)).1 = transU i j h (e i s).1)
    (heT : ∀ (i : A.Stages) (s : A.stageSections F₀ i),
      (eT (A.stageProjection F₀ hX i s)).1 = ιU i (e i s).1)
    (hU : Stacks.IsStagesColimit transU ιU) (hR : Stacks.IsStagesColimit transR ιR) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equiv F₀ hX _ _ e eT
    (fun i j h s => Subtype.ext (he i j h s)) (fun i s => Subtype.ext (heT i s))
    (Stacks.IsStagesColimit.equalizer hpt hqt hpi hqi hU hR)

/-- **The assertion of Stacks 07SI follows from equalizer presentations of its groups of global
sections over two systems of affine schemes, with no colimit assertion left as a hypothesis.**
Let `EU` and `ER` be inverse systems of affine schemes indexed by the stages at or beyond the
chosen index, with limiting cones `cU` and `cR`, and let `p, q` be two parallel families of maps
from the rings of global sections of the `EU` to those of the `ER`, compatible with the
transition maps and with the maps to the limits. If `Γ(Xᵢ, ℱᵢ)` is in bijection with the
equalizer of `p i` and `q i`, and `Γ(X, ℱ)` with the equalizer of `p'` and `q'`, compatibly with
the transition maps and the projections, then `Γ(X, ℱ)` is the filtered colimit of the
`Γ(Xᵢ, ℱᵢ)`. -/
theorem isSectionsColimit_of_equalizerPresentation_of_isAffine
    (hX : IsAlgebraicSpace B S hS X) (EU ER : (A.Stages)ᵒᵖ ⥤ Scheme.{u})
    [∀ a, IsAffine (EU.obj a)] [∀ a, IsAffine (ER.obj a)]
    {cU : Cone EU} (hcU : IsLimit cU) {cR : Cone ER} (hcR : IsLimit cR)
    {p q : ∀ i : A.Stages, (Γ(EU.obj (op i), ⊤) : Type u) → (Γ(ER.obj (op i), ⊤) : Type u)}
    {p' q' : (Γ(cU.pt, ⊤) : Type u) → (Γ(cR.pt, ⊤) : Type u)}
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (x : Γ(EU.obj (op i), ⊤)),
      p j ((EU.map (homOfLE h).op).appTop.hom x)
        = (ER.map (homOfLE h).op).appTop.hom (p i x))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (x : Γ(EU.obj (op i), ⊤)),
      q j ((EU.map (homOfLE h).op).appTop.hom x)
        = (ER.map (homOfLE h).op).appTop.hom (q i x))
    (hpi : ∀ (i : A.Stages) (x : Γ(EU.obj (op i), ⊤)),
      p' ((cU.π.app (op i)).appTop.hom x) = (cR.π.app (op i)).appTop.hom (p i x))
    (hqi : ∀ (i : A.Stages) (x : Γ(EU.obj (op i), ⊤)),
      q' ((cU.π.app (op i)).appTop.hom x) = (cR.π.app (op i)).appTop.hom (q i x))
    (e : ∀ i : A.Stages,
      A.stageSections F₀ i ≃ {x : Γ(EU.obj (op i), ⊤) // p i x = q i x})
    (eT : A.limitSections F₀ hX ≃ {x : Γ(cU.pt, ⊤) // p' x = q' x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (s : A.stageSections F₀ i),
      (e j (A.stageTransition F₀ i j h s)).1
        = (EU.map (homOfLE h).op).appTop.hom (e i s).1)
    (heT : ∀ (i : A.Stages) (s : A.stageSections F₀ i),
      (eT (A.stageProjection F₀ hX i s)).1 = (cU.π.app (op i)).appTop.hom (e i s).1) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equalizerPresentation F₀ hX hpt hqt hpi hqi e eT he heT
    (isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed EU cU hcU)
    (isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed ER cR hcR)

/-- **The assertion of Stacks 07SI follows from equalizer presentations of its groups of global
sections over an affine chart system and a quasi-compact quasi-separated relation system, with
no colimit assertion left as a hypothesis.** Let `EU` be an inverse system of affine schemes and
`ER` an inverse system of quasi-compact quasi-separated schemes with affine transition
morphisms, both indexed by the stages at or beyond the chosen index, with limiting cones `cU`
and `cR`, and let `p, q` be two parallel families of maps from the rings of global sections of
the `EU` to those of the `ER`, compatible with the transition maps and with the maps to the
limits. If `Γ(Xᵢ, ℱᵢ)` is in bijection with the equalizer of `p i` and `q i`, and `Γ(X, ℱ)` with
the equalizer of `p'` and `q'`, compatibly with the transition maps and the projections, then
`Γ(X, ℱ)` is the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`. -/
theorem isSectionsColimit_of_equalizerPresentation_of_qcqs
    (hX : IsAlgebraicSpace B S hS X) (EU ER : (A.Stages)ᵒᵖ ⥤ Scheme.{u})
    [∀ a, IsAffine (EU.obj a)]
    [∀ {a b : (A.Stages)ᵒᵖ} (g : a ⟶ b), _root_.AlgebraicGeometry.IsAffineHom (ER.map g)]
    [∀ a, CompactSpace (ER.obj a)] [∀ a, QuasiSeparatedSpace (ER.obj a)]
    {cU : Cone EU} (hcU : IsLimit cU) {cR : Cone ER} (hcR : IsLimit cR)
    {p q : ∀ i : A.Stages, (Γ(EU.obj (op i), ⊤) : Type u) → (Γ(ER.obj (op i), ⊤) : Type u)}
    {p' q' : (Γ(cU.pt, ⊤) : Type u) → (Γ(cR.pt, ⊤) : Type u)}
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (x : Γ(EU.obj (op i), ⊤)),
      p j ((EU.map (homOfLE h).op).appTop.hom x)
        = (ER.map (homOfLE h).op).appTop.hom (p i x))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (x : Γ(EU.obj (op i), ⊤)),
      q j ((EU.map (homOfLE h).op).appTop.hom x)
        = (ER.map (homOfLE h).op).appTop.hom (q i x))
    (hpi : ∀ (i : A.Stages) (x : Γ(EU.obj (op i), ⊤)),
      p' ((cU.π.app (op i)).appTop.hom x) = (cR.π.app (op i)).appTop.hom (p i x))
    (hqi : ∀ (i : A.Stages) (x : Γ(EU.obj (op i), ⊤)),
      q' ((cU.π.app (op i)).appTop.hom x) = (cR.π.app (op i)).appTop.hom (q i x))
    (e : ∀ i : A.Stages,
      A.stageSections F₀ i ≃ {x : Γ(EU.obj (op i), ⊤) // p i x = q i x})
    (eT : A.limitSections F₀ hX ≃ {x : Γ(cU.pt, ⊤) // p' x = q' x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (s : A.stageSections F₀ i),
      (e j (A.stageTransition F₀ i j h s)).1
        = (EU.map (homOfLE h).op).appTop.hom (e i s).1)
    (heT : ∀ (i : A.Stages) (s : A.stageSections F₀ i),
      (eT (A.stageProjection F₀ hX i s)).1 = (cU.π.app (op i)).appTop.hom (e i s).1) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equalizerPresentation F₀ hX hpt hqt hpi hqi e eT he heT
    (isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed EU cU hcU)
    (isStagesColimit_appTop_of_isLimit_of_directed ER cR hcR)

end LimitSituation

end AlgebraicGeometry.Space

end
