module

public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison
public import StacksFrontier.Topology.Sheaves.Stalk.CommRingPushout
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit
import Mathlib.Topology.Sheaves.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The one remaining input of flat base change for the extension algebra, proved

Let `g : X' ⟶ X` be a morphism of schemes and let `A` be a sheaf of commutative `𝒪_X`-algebras.
`Stacks.FundamentalGroup.algebraPullbackModuleComparison g A` is the canonical morphism of
`𝒪_{X'}`-modules

`g^*(module underlying A) ⟶ module underlying (g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'})`

and `StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison` reduces the
base-change clause of [Stacks, Tag 0EY6] — and with it the `algebraPullback_isQuasicoherent`
clause of [Stacks, Tag 01SA] along a flat morphism — to the single assertion that this
comparison is an **epimorphism**.  This file proves that assertion, for every morphism of
schemes and every algebra sheaf, with no flatness, quasi-compactness or quasi-separatedness
hypothesis.

**The content.**  Epimorphy is the statement that `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is generated, as an
`𝒪_{X'}`-module, by the image of `g⁻¹A`.  The proof has four steps.

* `Stacks.Sheaves.CommRingPushout.exists_list_germ_of_isPushout`:  the algebra pullback is a
  pushout of sheaves of commutative rings (`algebraPullback_isPushout`), the stalk functor
  preserves that pushout, and a pushout of commutative rings is a tensor product, so **every
  germ of the pullback algebra is a finite sum `Σ h(bᵢ) k(cᵢ)`** of products of a germ of
  `g⁻¹A` and a germ of `𝒪_{X'}`.
* `Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit`:  **every section of `g⁻¹A` agrees, near
  a point, with the image of a section of `A`**;  this is where the abstract left adjoint
  defining the inverse image is computed, via the stalk comparison of the adjunction unit.
* The adjoint transpose of the comparison is the module underlying the unit of the base-change
  adjunction for algebra sheaves (`homEquiv_algebraPullbackModuleComparison`), and that unit, on
  underlying sheaves of rings, is the unit of the inverse-image adjunction followed by
  `algebraPullbackMap` (`unit_right_eq`).  So **the image of the comparison contains the image
  of every section of `A`**, and it is an `𝒪_{X'}`-submodule, which closes the induction.
* `epi_of_isLocallySurjective`:  a morphism of sheaves of modules on a scheme whose image
  contains, locally around every point, the restriction of every section of the target is an
  epimorphism — `CategoryTheory.Sheaf.epi_of_isLocallySurjective` on the underlying morphism of
  sheaves of abelian groups, reflected along `SheafOfModules.toSheaf`.

## Main results

* `Stacks.FundamentalGroup.epi_of_isLocallySurjective` — local surjectivity of a morphism of
  `𝒪_Z`-modules implies epimorphy.
* `Stacks.FundamentalGroup.exists_restrict_mem_range_algebraPullbackModuleComparison` — **the
  generation statement**: every section of `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is, near every point of its
  domain, in the image of the comparison.
* `Stacks.FundamentalGroup.epi_algebraPullbackModuleComparison` — **the one obligation**: the
  comparison is an epimorphism.
* `Stacks.FundamentalGroup.flatBaseChange_algebraPullback` — the base-change clause of
  [Stacks, Tag 0EY6].
* `Stacks.FundamentalGroup.isQuasicoherent_algebraPullback` — the
  `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA] along a flat morphism.

## Implementation notes

`MemRange` is a predicate on the sections of the pullback algebra *as a sheaf of rings*, not on
the sections of its underlying module.  The two have the same underlying type, and restriction of
scalars changes neither the addition nor the restriction maps, so the four comparisons
`memRange_smul`, `memRange_add` and their relatives hold by `rfl`;  stating the predicate on the
ring side is what lets the output of `exists_list_germ_of_isPushout`, which is a product of ring
elements, be fed to it without transport.

The scalar action on the module underlying an algebra sheaf is multiplication by the image of the
scalar under the structure morphism;  that identity also holds by `rfl`, and it is what turns the
product `h(b) k(c)` of the pushout statement into the scalar multiple `c • h(b)` of an element of
the image.

**No `@[stacks]` attribute is placed in this file.**  The covering set of Tag 0EY6 and Tag 01SA
is for the lead to determine;  this file supplies one clause of each.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup

/-! ### Local surjectivity implies epimorphy for sheaves of modules on a scheme -/

/-- **A locally surjective morphism of `𝒪_Z`-modules is an epimorphism.**  The hypothesis is
local surjectivity in the form in which it arises — every section of the target is, near every
point of its domain, the image of a section of the source — and
`TopCat.Presheaf.isLocallySurjective_iff` turns it into
`CategoryTheory.Presheaf.IsLocallySurjective`, after which
`CategoryTheory.Sheaf.epi_of_isLocallySurjective` gives epimorphy of the underlying morphism of
sheaves of abelian groups and `SheafOfModules.toSheaf` reflects it. -/
public theorem epi_of_isLocallySurjective {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    (H : ∀ (U : Z.Opens) (t : Γ(N, U)) (x : Z), x ∈ U →
      ∃ (V : Z.Opens) (hV : V ≤ U), x ∈ V ∧
        ∃ s : Γ(M, V), φ.app V s = N.presheaf.map (homOfLE hV).op t) :
    Epi φ := by
  have hls0 : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mpr (fun U t x hx => by
      obtain ⟨V, hV, hxV, s, hs⟩ := H U t x hx
      exact ⟨V, hV, ⟨s, hs⟩, hxV⟩)
  have hls : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{u} Z.ringCatSheaf).map φ) :=
    hls0
  exact (SheafOfModules.toSheaf.{u} Z.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

/-! ### The inverse image inside the pullback algebra -/

section Inl

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (A : AlgebraSheaf X)

/-- **The canonical map `g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`**, i.e.
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` at `A`, with its target spelled as the
underlying sheaf of rings of the pullback algebra rather than as the value of a composite
functor.  The two spellings are definitionally equal and not syntactically equal, and the
unabbreviated one makes the ring operations on sections unavailable to instance search. -/
public def pullbackInl : (TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right ⟶
    ((algebraPullback g).obj A).right :=
  (algebraPullbackMap g).app A

/-- **The pullback algebra is the extension of scalars of the inverse image**, with the two legs
spelled as in `pullbackInl`.  This is `algebraPullback_isPushout`. -/
public theorem isPushout_pullbackInl :
    IsPushout ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).map A.hom)
      (inverseImageStructureMap g) (pullbackInl g A) ((algebraPullback g).obj A).hom :=
  algebraPullback_isPushout g A

/-- **The unit of the base-change adjunction for algebra sheaves, read on underlying sheaves of
rings, is the unit of the inverse-image adjunction followed by `pullbackInl`.**  Both are the
adjoint transpose of the identity, and `homEquiv_right` computes that transpose. -/
public theorem unit_right_eq :
    ((algebraPullbackPushforwardAdjunction g).unit.app A).right =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app A.right ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map (pullbackInl g A) :=
  Eq.trans
    (congrArg (fun t => Under.Hom.right t)
      ((algebraPullbackPushforwardAdjunction g).homEquiv_id A).symm)
    ((homEquiv_right g A ((algebraPullback g).obj A) (𝟙 _)).trans
      (Adjunction.homEquiv_unit _ _ _ _))

end Inl

/-! ### The image of the comparison on sections -/

section Range

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (A : AlgebraSheaf X)

/-- **Being in the image of the comparison.**  A section of the pullback algebra over `V`, read
as a section of its underlying `𝒪_{X'}`-module, which is the value of the comparison on a
section of the module pullback. -/
public def MemRange (V : X'.Opens)
    (t : ((algebraPullback g).obj A).right.obj.obj (op V)) : Prop :=
  ∃ s : Γ((Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A), V),
    (algebraPullbackModuleComparison g A).app V s = t

/-- Zero is in the image. -/
public theorem memRange_zero (V : X'.Opens) : MemRange g A V 0 := ⟨0, map_zero _⟩

/-- The image is closed under addition. -/
public theorem memRange_add (V : X'.Opens)
    {t₁ t₂ : ((algebraPullback g).obj A).right.obj.obj (op V)}
    (h₁ : MemRange g A V t₁) (h₂ : MemRange g A V t₂) : MemRange g A V (t₁ + t₂) := by
  obtain ⟨s₁, e₁⟩ := h₁
  obtain ⟨s₂, e₂⟩ := h₂
  exact ⟨s₁ + s₂, (map_add _ s₁ s₂).trans (by rw [e₁, e₂]; rfl)⟩

/-- The image is an `𝒪_{X'}`-submodule:  the action of a section of the structure sheaf is
multiplication by its image under the structure morphism of the pullback algebra. -/
public theorem memRange_smul (V : X'.Opens) (c : Γ(X', V))
    {t : ((algebraPullback g).obj A).right.obj.obj (op V)} (h : MemRange g A V t) :
    MemRange g A V ((((algebraPullback g).obj A).hom.hom.app (op V)) c * t) := by
  obtain ⟨s, e⟩ := h
  refine ⟨c • s, ?_⟩
  exact (Scheme.Modules.Hom.app_smul (algebraPullbackModuleComparison g A) c s).trans
    (congrArg (fun z => c • z) e)

/-- The image is closed under restriction. -/
public theorem memRange_res {V V' : X'.Opens} (i : V' ⟶ V)
    {t : ((algebraPullback g).obj A).right.obj.obj (op V)} (h : MemRange g A V t) :
    MemRange g A V' ((((algebraPullback g).obj A).right.obj.map i.op) t) := by
  obtain ⟨s, e⟩ := h
  refine ⟨(((Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A)).presheaf.map
    i.op) s, ?_⟩
  refine (NatTrans.naturality_apply
    (algebraPullbackModuleComparison g A).mapPresheaf i.op s).trans ?_
  exact congrArg (fun z => ((AlgebraSheaf.underlyingModule
    ((algebraPullback g).obj A)).presheaf.map i.op) z) e

/-- **The image contains the image of every section of `A`.**  The adjoint transpose of the
comparison is the module underlying the unit of the base-change adjunction for algebra sheaves,
and that unit, on underlying rings, is the unit of the inverse-image adjunction followed by
`pullbackInl`. -/
public theorem memRange_unit (U : X.Opens) (a : A.right.obj.obj (op U)) :
    MemRange g A (g ⁻¹ᵁ U)
      (((pullbackInl g A).hom.app (op (g ⁻¹ᵁ U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            g.base).unit.app A.right).hom.app (op U)) a)) := by
  refine ⟨((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
    (AlgebraSheaf.underlyingModule A)).app U a, ?_⟩
  have key : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (AlgebraSheaf.underlyingModule A)) ≫
      (Scheme.Modules.pushforward g).map (algebraPullbackModuleComparison g A) =
      AlgebraSheaf.underlyingModuleMap ((algebraPullbackPushforwardAdjunction g).unit.app A) :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (homEquiv_algebraPullbackModuleComparison g A)
  have key2 := congrArg (fun z => Scheme.Modules.Hom.app z U) key
  have key3 := congrArg (fun z => (ConcreteCategory.hom z) a) key2
  refine key3.trans ?_
  have hu := congrArg (fun z => CategoryTheory.InducedCategory.Hom.hom z) (unit_right_eq g A)
  have hu2 := congrArg (fun z => z.app (op U)) hu
  exact congrArg (fun z => (CommRingCat.Hom.hom z) a) hu2

end Range

/-! ### The germs in the image -/

section Germ

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (A : AlgebraSheaf X) (x : X')

/-- **A germ of the pullback algebra which is the germ of a section in the image of the
comparison.** -/
public def MemRangeGerm (q : ((algebraPullback g).obj A).right.presheaf.stalk x) : Prop :=
  ∃ (V : X'.Opens) (hx : x ∈ V) (t : ((algebraPullback g).obj A).right.obj.obj (op V)),
    q = ((algebraPullback g).obj A).right.presheaf.germ V x hx t ∧ MemRange g A V t

/-- Zero is such a germ. -/
public theorem memRangeGerm_zero : MemRangeGerm g A x 0 :=
  ⟨⊤, trivial, 0, (map_zero _).symm, memRange_zero g A ⊤⟩

/-- Such germs are closed under addition. -/
public theorem memRangeGerm_add {q₁ q₂ : ((algebraPullback g).obj A).right.presheaf.stalk x}
    (h₁ : MemRangeGerm g A x q₁) (h₂ : MemRangeGerm g A x q₂) :
    MemRangeGerm g A x (q₁ + q₂) := by
  obtain ⟨V₁, hx₁, t₁, hq₁, hm₁⟩ := h₁
  obtain ⟨V₂, hx₂, t₂, hq₂, hm₂⟩ := h₂
  refine ⟨V₁ ⊓ V₂, ⟨hx₁, hx₂⟩,
    (((algebraPullback g).obj A).right.obj.map (homOfLE inf_le_left).op) t₁ +
      (((algebraPullback g).obj A).right.obj.map (homOfLE inf_le_right).op) t₂, ?_, ?_⟩
  · refine Eq.trans (congrArg₂ (fun a b => a + b) hq₁ hq₂) ?_
    refine Eq.trans ?_ (map_add _ _ _).symm
    exact congrArg₂ (fun a b => a + b)
      (((algebraPullback g).obj A).right.presheaf.germ_res_apply
        (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) x ⟨hx₁, hx₂⟩ t₁).symm
      (((algebraPullback g).obj A).right.presheaf.germ_res_apply
        (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) x ⟨hx₁, hx₂⟩ t₂).symm
  · exact memRange_add g A _ (memRange_res g A _ hm₁) (memRange_res g A _ hm₂)

/-- The stalk map of a morphism of presheaves sends a germ to the germ of the image of its
restriction. -/
private theorem stalkFunctor_map_eq_germ_res {Y : TopCat.{u}}
    {F G : TopCat.Presheaf CommRingCat.{u} Y} (φ : F ⟶ G) {x : Y}
    {V W : TopologicalSpace.Opens Y} (hxW : x ∈ W)
    (i : W ⟶ V) (s : F.obj (op V)) (b : F.stalk x) (h : F.germ V x (i.le hxW) s = b) :
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map φ b =
      G.germ W x hxW (φ.app (op W) (F.map i.op s)) := by
  subst h
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x _ φ s).trans
    ((G.germ_res_apply i x hxW _).symm.trans
      (congrArg (G.germ W x hxW) (NatTrans.naturality_apply φ i.op s).symm))

/-- **The generators are such germs.**  A product of the image of a germ of `g⁻¹A` and the image
of a germ of `𝒪_{X'}` is the germ of a section in the image of the comparison:  the germ of
`g⁻¹A` is, near `x`, the image of a section `a` of `A`, whose image under `pullbackInl` lies in
the image of the comparison by `memRange_unit`, and multiplication by the image of a section of
`𝒪_{X'}` is the scalar action. -/
public theorem memRangeGerm_mul
    (b : ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right).presheaf.stalk x)
    (c : X'.sheaf.presheaf.stalk x) :
    MemRangeGerm g A x
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (pullbackInl g A).hom) b *
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          ((algebraPullback g).obj A).hom.hom) c) := by
  obtain ⟨V₁, hx₁, b₀, hb₀⟩ :=
    ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right).presheaf.exists_germ_eq b
  obtain ⟨U, W, hxW, iV, iU, a, hEq⟩ :=
    Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit g.base A.right x V₁ hx₁ b₀
  obtain ⟨V₂, hx₂, c₀, hc₀⟩ := X'.sheaf.presheaf.exists_germ_eq c
  have hxV : x ∈ W ⊓ V₂ := ⟨hxW, hx₂⟩
  refine ⟨W ⊓ V₂, hxV,
    ((pullbackInl g A).hom.app (op (W ⊓ V₂)))
        ((((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right).presheaf.map
          ((homOfLE (inf_le_left : W ⊓ V₂ ≤ W)) ≫ iV).op) b₀) *
      (((algebraPullback g).obj A).hom.hom.app (op (W ⊓ V₂)))
        ((X'.sheaf.presheaf.map (homOfLE (inf_le_right : W ⊓ V₂ ≤ V₂)).op) c₀), ?_, ?_⟩
  · exact (congrArg₂ (· * ·)
      (stalkFunctor_map_eq_germ_res (pullbackInl g A).hom hxV
        (homOfLE (inf_le_left : W ⊓ V₂ ≤ W) ≫ iV) b₀ b hb₀)
      (stalkFunctor_map_eq_germ_res ((algebraPullback g).obj A).hom.hom hxV
        (homOfLE (inf_le_right : W ⊓ V₂ ≤ V₂)) c₀ c hc₀)).trans (map_mul _ _ _).symm
  · have hβ : (((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right).presheaf.map
          ((homOfLE (inf_le_left : W ⊓ V₂ ≤ W)) ≫ iV).op) b₀ =
        (((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A.right).presheaf.map
          ((homOfLE (inf_le_left : W ⊓ V₂ ≤ W)) ≫ iU).op)
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            g.base).unit.app A.right).hom.app (op U)) a) :=
      ((Functor.map_comp_apply _ iV.op (homOfLE (inf_le_left : W ⊓ V₂ ≤ W)).op b₀).trans
        (congrArg (fun z => (((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj
          A.right).presheaf.map (homOfLE (inf_le_left : W ⊓ V₂ ≤ W)).op) z) hEq)).trans
        (Functor.map_comp_apply _ iU.op (homOfLE (inf_le_left : W ⊓ V₂ ≤ W)).op _).symm
    have hnat := NatTrans.naturality_apply (pullbackInl g A).hom
      ((homOfLE (inf_le_left : W ⊓ V₂ ≤ W)) ≫ iU).op
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        g.base).unit.app A.right).hom.app (op U)) a)
    have hmem := memRange_smul g A (W ⊓ V₂)
      ((X'.sheaf.presheaf.map (homOfLE (inf_le_right : W ⊓ V₂ ≤ V₂)).op) c₀)
      (memRange_res g A ((homOfLE (inf_le_left : W ⊓ V₂ ≤ W)) ≫ iU)
        (memRange_unit g A U a))
    refine Eq.mpr (congrArg (MemRange g A (W ⊓ V₂)) ?_) hmem
    refine Eq.trans (mul_comm _ _) ?_
    exact congrArg (fun z => (((algebraPullback g).obj A).hom.hom.app (op (W ⊓ V₂)))
        ((X'.sheaf.presheaf.map (homOfLE (inf_le_right : W ⊓ V₂ ≤ V₂)).op) c₀) * z)
      ((congrArg (fun z => ((pullbackInl g A).hom.app (op (W ⊓ V₂))) z) hβ).trans hnat)

/-- **Every germ of the pullback algebra is the germ of a section in the image of the
comparison.**  The pullback algebra is a pushout of sheaves of commutative rings, so by
`Stacks.Sheaves.CommRingPushout.exists_list_germ_of_isPushout` every germ is a finite sum of
products of the images of a germ of `g⁻¹A` and a germ of `𝒪_{X'}`;  each such product is handled
by `memRangeGerm_mul` and the sum by `memRangeGerm_add`. -/
public theorem memRangeGerm_all (q : ((algebraPullback g).obj A).right.presheaf.stalk x) :
    MemRangeGerm g A x q := by
  obtain ⟨L, hL⟩ := Stacks.Sheaves.CommRingPushout.exists_list_germ_of_isPushout x
    (isPushout_pullbackInl g A) q
  refine Eq.mpr (congrArg (MemRangeGerm g A x) hL) ?_
  clear hL
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact memRangeGerm_zero g A x
  | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact memRangeGerm_add g A x (memRangeGerm_mul g A x p.1 p.2) ih

end Germ

/-! ### Local surjectivity, and the epimorphism -/

section Epi

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (A : AlgebraSheaf X)

/-- **The generation statement.**  Every section of `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` over an open `V`
agrees, on a neighbourhood of any prescribed point of `V`, with a section in the image of the
comparison.  No flatness, quasi-compactness or quasi-separatedness hypothesis occurs. -/
public theorem exists_restrict_memRange (V : X'.Opens)
    (t : ((algebraPullback g).obj A).right.obj.obj (op V)) (x : X') (hx : x ∈ V) :
    ∃ (W : X'.Opens) (hW : W ≤ V), x ∈ W ∧
      MemRange g A W ((((algebraPullback g).obj A).right.obj.map (homOfLE hW).op) t) := by
  obtain ⟨V', hx', t', hq, hm⟩ := memRangeGerm_all g A x
    (((algebraPullback g).obj A).right.presheaf.germ V x hx t)
  obtain ⟨W, hxW, iV', iV, hEq⟩ :=
    ((algebraPullback g).obj A).right.presheaf.germ_eq x hx' hx t' t hq.symm
  refine ⟨W, iV.le, hxW, ?_⟩
  have h1 : MemRange g A W ((((algebraPullback g).obj A).right.obj.map iV.op) t) :=
    Eq.mpr (congrArg (MemRange g A W) hEq.symm) (memRange_res g A iV' hm)
  exact Eq.mpr (congrArg (fun i : W ⟶ V => MemRange g A W
    ((((algebraPullback g).obj A).right.obj.map i.op) t))
    (Subsingleton.elim (homOfLE iV.le) iV)) h1

/-- **The one remaining input of [Stacks, Tag 0EY6] and of the base-change clause of
[Stacks, Tag 01SA]: the canonical comparison is an epimorphism.**  For every morphism of schemes
`g : X' ⟶ X` and every sheaf of commutative `𝒪_X`-algebras `A`, the canonical morphism

`g^*(module underlying A) ⟶ module underlying (g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'})`

is an epimorphism of `𝒪_{X'}`-modules;  equivalently, `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is generated as
an `𝒪_{X'}`-module by the image of `g⁻¹A`. -/
public theorem epi_algebraPullbackModuleComparison :
    Epi (algebraPullbackModuleComparison g A) := by
  refine epi_of_isLocallySurjective _ (fun U t x hx => ?_)
  obtain ⟨W, hW, hxW, hm⟩ := exists_restrict_memRange g A U t x hx
  obtain ⟨s, hs⟩ := hm
  exact ⟨W, hW, hxW, s, hs⟩

end Epi

/-! ### The two clauses of Tag 0EY6 -/

section Closure

/-- **The base-change clause of [Stacks, Tag 0EY6].**  For a quasi-compact quasi-separated
morphism `f : V ⟶ Y` and a flat morphism `q : Y' ⟶ Y`, the pushed-forward structure sheaf of the
base change is the extension of scalars of the inverse image of `f_* 𝒪_V`. -/
@[stacks 0EY6 "flat_base_change"]
public theorem flatBaseChange_algebraPullback {V Y Y' : Scheme.{u}} (f : V ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (q : Y' ⟶ Y) [Flat q] :
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat q.base).map (pushforwardAlgebra f).hom)
      (inverseImageStructureMap q)
      (pushforwardBaseChangeMap q (Over.mk f))
      (pushforwardAlgebra ((Over.pullback q).obj (Over.mk f)).hom).hom :=
  flatBaseChange_of_epi_comparison
    (fun q' _ V' _ _ => epi_algebraPullbackModuleComparison q' (pushforwardAlgebra V'.hom)) f q

/-- **The `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA] along a flat
morphism.**  The pullback of a quasi-coherent sheaf of algebras along a flat morphism is
quasi-coherent. -/
public theorem isQuasicoherent_algebraPullback {X X' : Scheme.{u}} (g : X' ⟶ X) [Flat g]
    (A : AlgebraSheaf X) [A.IsQuasicoherent] :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  isQuasicoherent_algebraPullback_of_epi_comparison
    (fun q' _ V' _ _ => epi_algebraPullbackModuleComparison q' (pushforwardAlgebra V'.hom)) g A

end Closure

end Stacks.FundamentalGroup

end
