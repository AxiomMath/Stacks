module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiDatumAssembly
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assembling the Zariski descent datum of Stacks 023T

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiDatumAssembly.lean` builds, for a
quasi-coherent descent datum `D` relative to an fpqc covering family `𝒰` of a scheme `S`, every
field of the Zariski descent datum that
`AlgebraicGeometry.QuasicoherentDescentData.ZariskiDescentDatumOverAffineCover` asks for, with a
single restriction: its transition `…localTransition` is defined only over a scheme which maps to
a member of `𝒰`.  This file records what remains, namely the descent of that transition along the
base change of `𝒰`, and assembles the datum from it.

What is *not* done here is the gluing itself.  It is isolated as
`AlgebraicGeometry.QuasicoherentDescentData.ZariskiTransitionOverAnyBase`, a statement with no
other content than the existence of that one transition together with its restrictions, and
everything else — the datum, its three conditions, and the isomorphism over the affine-open
refinement — is derived from it.  In one checkable sentence: **what is missing is the existence
of a morphism between the pullbacks of two chosen local solutions to an arbitrary scheme over
`S` whose restriction to each member of the base change of `𝒰` is the corresponding
`…localTransition`; its uniqueness is `transition_ext` below, which is a theorem.**

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentData.ZariskiTransitionOverAnyBase`: the one remaining
  statement — the transition over an arbitrary scheme over `S`, restricting to
  `…localTransition` over every scheme mapping to a member of `𝒰`.
* `AlgebraicGeometry.QuasicoherentDescentData.zariskiTransition`: the transition that statement
  provides, chosen once and for all, and `…zariskiDatum`, the Zariski descent datum built from
  it.
* `AlgebraicGeometry.QuasicoherentDescentData.zariskiDatumIso`: the isomorphism of its
  restriction to the affine-open refinement with the restriction of `D`.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.pullHom_ext_of_mem_fpqcPrecoverage`: **a morphism
  between pullbacks of quasi-coherent sheaves of modules is determined by its restrictions to
  the members of an fpqc covering family of the base.**  This is the faithfulness half of Stacks
  023T in the `pullHom` spelling, and it is what makes the datum's conditions formalities.
* `AlgebraicGeometry.QuasicoherentDescentData.hom_comm_of_pullHom_comm`: **a family of morphisms
  between the components of two restricted descent data is a morphism of descent data as soon as
  it intertwines their transitions**, in the `pullHom` spelling.
* `AlgebraicGeometry.QuasicoherentDescentData.pullHom_zariskiTransition_eq`,
  `…zariskiTransition_self` and `…zariskiTransition_comp`: **the three conditions of the datum
  being built**, each by reduction along the base change of `𝒰`.
* `AlgebraicGeometry.QuasicoherentDescentData.zariskiDescentDatumOverAffineCover_of_transition`:
  **`…ZariskiDescentDatumOverAffineCover` holds as soon as that one transition exists**, hence
  so does the effectivity half of Stacks 023T.

## Implementation notes

Everything is read in the `pullHom` spelling of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat` and at the level of
`CategoryTheory.Pseudofunctor.DescentData` rather than of
`AlgebraicGeometry.QuasicoherentDescentData`, because the predicate cutting out the
quasi-coherent descent data mentions `AlgebraicGeometry.Scheme.ringCatSheaf`, whose type is not
type-correct at the `implicit` transparency level.  For the same reason the two statements about
the affine-open refinement that mention an index of the affine open covering —
`pullbackSnd_comp_f_eq` and `pullHom_affineOpenComponent_comp` — are stated separately with that
index properly typed:
inside `zariskiDatumIso` the index is a component of a `Sigma` over
`(AlgebraicGeometry.affineZeroHypercover S).I₀`, and no `rw` can be performed on a goal
mentioning it.

`…rawPullFunctor_obj_hom` is stated with the two index types in independent universes: the
affine-open refinement is indexed in `max u v`, the affine open covering in `u` and the given
family in `v`.

No `stacks` attribute is placed: the unconditional results here are not clauses of a tag, and the
chain to Stacks 023T carries a hypothesis.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  Pseudofunctor.LocallyDiscreteOpToCat

universe w₃ w₂ w₁ v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-! ### Separatedness along an fpqc covering -/

/-- **A morphism between pullbacks of quasi-coherent sheaves of modules is determined by its
restrictions to the members of an fpqc covering family of the base.**

This is the faithfulness half of [Stacks, Tag 023T],
`…nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`, read through
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom`: the restriction of a
morphism to a member of the family is the component at that member of the morphism of canonical
descent data it induces.  It is `AlgebraicGeometry.pullHom_ext` with the Zariski covering
replaced by an arbitrary fpqc one, at the cost of quasi-coherence of the two sheaves. -/
@[sga "1 VIII 1.2" "Injectivity of Hom_S(F"]
theorem pullHom_ext_of_mem_fpqcPrecoverage {V : Scheme.{u}} (𝒱 : PreZeroHypercover.{v} V)
    (h𝒱 : 𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} V) {Z₁ Z₂ : Scheme.{u}}
    {M₁ : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
    {M₂ : modulePullbackPseudofunctor.obj (.mk (op Z₂))} {g₁ : V ⟶ Z₁} {g₂ : V ⟶ Z₂}
    (hM₁ : (pullMod g₁ M₁).IsQuasicoherent) (hM₂ : (pullMod g₂ M₂).IsQuasicoherent)
    (gf₁ : ∀ k, 𝒱.X k ⟶ Z₁) (gf₂ : ∀ k, 𝒱.X k ⟶ Z₂)
    (h₁ : ∀ k, 𝒱.f k ≫ g₁ = gf₁ k) (h₂ : ∀ k, 𝒱.f k ≫ g₂ = gf₂ k)
    {ψ ψ' : pullMod g₁ M₁ ⟶ pullMod g₂ M₂}
    (h : ∀ k, pullHom ψ (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k) =
      pullHom ψ' (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k)) : ψ = ψ' := by
  obtain ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage 𝒱 h𝒱
  have := hff.faithful
  let A : (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory :=
    ⟨pullMod g₁ M₁, hM₁⟩
  let B : (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory :=
    ⟨pullMod g₂ M₂, hM₂⟩
  have key : (canonicalDescentFunctor 𝒱.f).map (ObjectProperty.homMk (X := A) (Y := B) ψ) =
      (canonicalDescentFunctor 𝒱.f).map (ObjectProperty.homMk (X := A) (Y := B) ψ') := by
    apply ObjectProperty.hom_ext
    refine Pseudofunctor.DescentData.hom_ext fun k ↦ ?_
    have e : (modulePullbackPseudofunctor.map (𝒱.f k).op.toLoc).toFunctor.map ψ =
        (modulePullbackPseudofunctor.map (𝒱.f k).op.toLoc).toFunctor.map ψ' := by
      rw [map_eq_pullHom ψ (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k),
        map_eq_pullHom ψ' (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k), h k]
    exact e
  exact congrArg (fun φ : A ⟶ B ↦ φ.hom) ((canonicalDescentFunctor 𝒱.f).map_injective key)

/-! ### Morphisms between two restricted descent data -/

section Dictionary

variable {T T' W : Scheme.{u}} {𝒱 : PreZeroHypercover.{w₁} T} {𝒲 : PreZeroHypercover.{w₂} T'}
  {𝒳 : PreZeroHypercover.{w₃} W}

/-- **A family of morphisms between the components of two restricted descent data is a morphism
of descent data as soon as it intertwines the transitions of the two data, in the `pullHom`
spelling.**

Both `…rawPullFunctor_obj_hom` and
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom` conjugate by the comparison
isomorphisms of the pullback pseudofunctor, and the conjugating isomorphisms cancel in pairs; the
`CategoryTheory.Pseudofunctor.DescentData.Hom.comm` condition is therefore equivalent to the
displayed identity between pullbacks of the components, which mentions no comparison isomorphism
at all.  This is the two-restriction companion of `…pullHom_hom_comp_eq`, whose source is a
canonical datum rather than a restricted one. -/
theorem hom_comm_of_pullHom_comm {k : W ⟶ T} (Φ : 𝒳.HomOver 𝒱 k) {k' : W ⟶ T'}
    (Φ' : 𝒳.HomOver 𝒲 k') (E : modulePullbackPseudofunctor.DescentData 𝒱.f)
    (E' : modulePullbackPseudofunctor.DescentData 𝒲.f)
    (φ : ∀ j, pullMod (Φ.h₀ j) (E.obj (Φ.s₀ j)) ⟶ pullMod (Φ'.h₀ j) (E'.obj (Φ'.s₀ j)))
    {Y : Scheme.{u}} (y : Y ⟶ W) {j₁ j₂ : 𝒳.I₀} (d₁ : Y ⟶ 𝒳.X j₁) (d₂ : Y ⟶ 𝒳.X j₂)
    (hd₁ : d₁ ≫ 𝒳.f j₁ = y) (hd₂ : d₂ ≫ 𝒳.f j₂ = y)
    (q : Y ⟶ T) (hq : y ≫ k = q) (q' : Y ⟶ T') (hq' : y ≫ k' = q')
    (b₁ : Y ⟶ 𝒱.X (Φ.s₀ j₁)) (b₂ : Y ⟶ 𝒱.X (Φ.s₀ j₂))
    (hb₁ : d₁ ≫ Φ.h₀ j₁ = b₁) (hb₂ : d₂ ≫ Φ.h₀ j₂ = b₂)
    (hq₁ : b₁ ≫ 𝒱.f (Φ.s₀ j₁) = q) (hq₂ : b₂ ≫ 𝒱.f (Φ.s₀ j₂) = q)
    (b₁' : Y ⟶ 𝒲.X (Φ'.s₀ j₁)) (b₂' : Y ⟶ 𝒲.X (Φ'.s₀ j₂))
    (hb₁' : d₁ ≫ Φ'.h₀ j₁ = b₁') (hb₂' : d₂ ≫ Φ'.h₀ j₂ = b₂')
    (hq₁' : b₁' ≫ 𝒲.f (Φ'.s₀ j₁) = q') (hq₂' : b₂' ≫ 𝒲.f (Φ'.s₀ j₂) = q')
    (key : pullHom (φ j₁) d₁ b₁ b₁' hb₁ hb₁' ≫ E'.hom q' b₁' b₂' hq₁' hq₂' =
      E.hom q b₁ b₂ hq₁ hq₂ ≫ pullHom (φ j₂) d₂ b₂ b₂' hb₂ hb₂') :
    (modulePullbackPseudofunctor.map d₁.op.toLoc).toFunctor.map (φ j₁) ≫
        ((Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
            (f := 𝒲.f) (p := k') (f' := 𝒳.f) (α := Φ'.s₀) (p' := Φ'.h₀) Φ'.w₀).obj E').hom
          y d₁ d₂ hd₁ hd₂ =
      ((Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
            (f := 𝒱.f) (p := k) (f' := 𝒳.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀).obj E).hom
          y d₁ d₂ hd₁ hd₂ ≫
        (modulePullbackPseudofunctor.map d₂.op.toLoc).toFunctor.map (φ j₂) := by
  have key₂ : ((pullModComp d₁ (Φ.h₀ j₁) b₁ hb₁ (E.obj (Φ.s₀ j₁))).inv ≫
        pullHom (φ j₁) d₁ b₁ b₁' hb₁ hb₁' ≫
          (pullModComp d₁ (Φ'.h₀ j₁) b₁' hb₁' (E'.obj (Φ'.s₀ j₁))).hom) ≫
      ((pullModComp d₁ (Φ'.h₀ j₁) b₁' hb₁' (E'.obj (Φ'.s₀ j₁))).inv ≫
        E'.hom q' b₁' b₂' hq₁' hq₂' ≫
          (pullModComp d₂ (Φ'.h₀ j₂) b₂' hb₂' (E'.obj (Φ'.s₀ j₂))).hom) =
      ((pullModComp d₁ (Φ.h₀ j₁) b₁ hb₁ (E.obj (Φ.s₀ j₁))).inv ≫
        E.hom q b₁ b₂ hq₁ hq₂ ≫
          (pullModComp d₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).hom) ≫
      ((pullModComp d₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).inv ≫
        pullHom (φ j₂) d₂ b₂ b₂' hb₂ hb₂' ≫
          (pullModComp d₂ (Φ'.h₀ j₂) b₂' hb₂' (E'.obj (Φ'.s₀ j₂))).hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (pullHom (φ j₁) d₁ b₁ b₁' hb₁ hb₁'), key, Category.assoc]
  rw [← map_eq_pullHom' (φ j₁) d₁ b₁ b₁' hb₁ hb₁',
    ← map_eq_pullHom' (φ j₂) d₂ b₂ b₂' hb₂ hb₂'] at key₂
  rwa [rawPullFunctor_obj_hom Φ' E' y d₁ d₂ hd₁ hd₂ q' hq' b₁' b₂' hb₁' hb₂' hq₁' hq₂',
    rawPullFunctor_obj_hom Φ E y d₁ d₂ hd₁ hd₂ q hq b₁ b₂ hb₁ hb₂ hq₁ hq₂]

end Dictionary

/-! ### The one remaining step -/

/-- **The descent of the transition along the base change of the covering family**: the one step
the assembly of the Zariski descent datum of Stacks 023T still needs.

`AlgebraicGeometry.QuasicoherentDescentData.localTransition` is a transition between the chosen
local solutions over `U a` and `U b` only over a scheme which maps to a *member of `𝒰`*; the
datum `ZariskiDescentDatumOverAffineCover` asks for one over an arbitrary scheme over `S`.  Over
such a scheme `V` the base change `𝒰.pullback₁ q` is an fpqc covering of `V`, the local
transitions over its members do not depend on the member by `…localTransition_eq` and are
compatible with pullback by `…pullHom_localTransition`, so they glue; this statement is exactly
that gluing, and it is the only thing
`…zariskiDescentDatumOverAffineCover_of_transition` below assumes. -/
abbrev ZariskiTransitionOverAnyBase : Prop :=
  ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (D : QuasicoherentDescentData 𝒰.f)
    (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b),
      g₁ ≫ S.affineCover.f a = q → g₂ ≫ S.affineCover.f b = q →
        ∃ τ : pullMod g₁ (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
            pullMod g₂ (affineOpenModule 𝒰 h𝒰 D b).obj,
          ∀ {W : Scheme.{u}} (m : W ⟶ V) (i : 𝒰.I₀) (c : W ⟶ 𝒰.X i)
            (m₁ : W ⟶ S.affineCover.X a) (m₂ : W ⟶ S.affineCover.X b)
            (hm₁ : m ≫ g₁ = m₁) (hm₂ : m ≫ g₂ = m₂)
            (h₁ : m₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i)
            (h₂ : m₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i),
              pullHom τ m m₁ m₂ hm₁ hm₂ = localTransition 𝒰 h𝒰 D a b m₁ m₂ i c h₁ h₂

/-! ### Descending the transitions -/

section Assembly

variable {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
  (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (D : QuasicoherentDescentData 𝒰.f)

/-- **The transition between two local solutions is the composite of a comparison with an
inverse comparison**, which is how `AlgebraicGeometry.QuasicoherentDescentData.localTransition`
is defined; stated so that it can be rewritten with. -/
theorem localTransition_eq_comp (a b : S.affineCover.I₀) {V : Scheme.{u}}
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b) (i : 𝒰.I₀) (c : V ⟶ 𝒰.X i)
    (h₁ : g₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (h₂ : g₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i) :
    localTransition 𝒰 h𝒰 D a b g₁ g₂ i c h₁ h₂ =
      localComparison 𝒰 h𝒰 D a i g₁ c h₁ ≫ localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂ :=
  rfl

/-- **The pullback of a chosen local solution is quasi-coherent**, quasi-coherence being stable
under pullback (Stacks 01BG). -/
theorem isQuasicoherent_pullMod_affineOpenModule (a : S.affineCover.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) :
    (pullMod g (affineOpenModule 𝒰 h𝒰 D a).obj).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback g _ (affineOpenModule 𝒰 h𝒰 D a).property

/-- **A morphism between the pullbacks of two chosen local solutions to a scheme over `S` is
determined by its restrictions to the base change of `𝒰`**, that base change being an fpqc
covering of that scheme.  This is `pullHom_ext_of_mem_fpqcPrecoverage` at the covering family the
remaining step descends along, and it is what makes every field of the datum below a formality
once the transition itself is available. -/
theorem transition_ext (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    {τ τ' : pullMod g₁ (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
      pullMod g₂ (affineOpenModule 𝒰 h𝒰 D b).obj}
    (h : ∀ i : 𝒰.I₀,
      pullHom τ (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) rfl rfl =
        pullHom τ' (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g₁)
          (pullback.fst q (𝒰.f i) ≫ g₂) rfl rfl) : τ = τ' :=
  pullHom_ext_of_mem_fpqcPrecoverage (𝒰.pullback₁ q) (mem_fpqcPrecoverage_pullback₁ 𝒰 h𝒰 q)
    (isQuasicoherent_pullMod_affineOpenModule 𝒰 h𝒰 D a g₁)
    (isQuasicoherent_pullMod_affineOpenModule 𝒰 h𝒰 D b g₂)
    (fun i ↦ pullback.fst q (𝒰.f i) ≫ g₁) (fun i ↦ pullback.fst q (𝒰.f i) ≫ g₂)
    (fun _ ↦ rfl) (fun _ ↦ rfl) h

/-- **The chosen comparison at a member of the affine-open refinement, as an isomorphism.**  Its
two directions are `…affineOpenComponent` and `…affineOpenComponentInv`, which are mutually
inverse because they are the components of an isomorphism of descent data. -/
noncomputable def affineOpenComponentIso (a : S.affineCover.I₀) (i : 𝒰.I₀) :
    pullMod (pullback.fst (S.affineCover.f a) (𝒰.f i)) (affineOpenModule 𝒰 h𝒰 D a).obj ≅
      pullMod (pullback.snd (S.affineCover.f a) (𝒰.f i)) (D.obj.obj i) where
  hom := affineOpenComponent 𝒰 h𝒰 D a i
  inv := affineOpenComponentInv 𝒰 h𝒰 D a i
  hom_inv_id := affineOpenComponent_comp 𝒰 h𝒰 D a i
  inv_hom_id := affineOpenComponentInv_comp 𝒰 h𝒰 D a i

/-- **A morphism to a member of the affine-open refinement lying over `y : Y ⟶ S` through the
first projection lies over `y` through the second one too**, the fibre-product square
commuting. -/
theorem pullbackSnd_comp_f_eq (a : S.affineCover.I₀) (i : 𝒰.I₀) {Y : Scheme.{u}}
    (d : Y ⟶ pullback (S.affineCover.f a) (𝒰.f i)) (y : Y ⟶ S)
    (hd : (d ≫ pullback.fst (S.affineCover.f a) (𝒰.f i)) ≫ S.affineCover.f a = y) :
    (d ≫ pullback.snd (S.affineCover.f a) (𝒰.f i)) ≫ 𝒰.f i = y := by
  rwa [Category.assoc, ← pullback.condition, ← Category.assoc]

variable (hT : ZariskiTransitionOverAnyBase.{v, u})

/-- **The descended transition between two chosen local solutions, over an arbitrary scheme over
`S`**: the morphism the remaining step provides, chosen once and for all. -/
noncomputable def zariskiTransition (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q) :
    pullMod g₁ (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
      pullMod g₂ (affineOpenModule 𝒰 h𝒰 D b).obj :=
  (hT 𝒰 h𝒰 D a b q g₁ g₂ hg₁ hg₂).choose

/-- **The descended transition restricts to `…localTransition` over every scheme mapping to a
member of `𝒰`**: the defining property of `zariskiTransition`. -/
theorem pullHom_zariskiTransition (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q)
    {W : Scheme.{u}} (m : W ⟶ V) (i : 𝒰.I₀) (c : W ⟶ 𝒰.X i)
    (m₁ : W ⟶ S.affineCover.X a) (m₂ : W ⟶ S.affineCover.X b)
    (hm₁ : m ≫ g₁ = m₁) (hm₂ : m ≫ g₂ = m₂)
    (h₁ : m₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (h₂ : m₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i) :
    pullHom (zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂) m m₁ m₂ hm₁ hm₂ =
      localTransition 𝒰 h𝒰 D a b m₁ m₂ i c h₁ h₂ :=
  (hT 𝒰 h𝒰 D a b q g₁ g₂ hg₁ hg₂).choose_spec m i c m₁ m₂ hm₁ hm₂ h₁ h₂

/-- The descended transition restricted along the first projection of the base change of `𝒰` is
the corresponding `…localTransition`. -/
private theorem pullHom_zariskiTransition_fst (a b : S.affineCover.I₀) {V : Scheme.{u}}
    (q : V ⟶ S) (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q) (i : 𝒰.I₀) :
    pullHom (zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂) (pullback.fst q (𝒰.f i))
        (pullback.fst q (𝒰.f i) ≫ g₁) (pullback.fst q (𝒰.f i) ≫ g₂) rfl rfl =
      localTransition 𝒰 h𝒰 D a b (pullback.fst q (𝒰.f i) ≫ g₁) (pullback.fst q (𝒰.f i) ≫ g₂) i
        (pullback.snd q (𝒰.f i)) (by rw [Category.assoc, hg₁, pullback.condition])
        (by rw [Category.assoc, hg₂, pullback.condition]) :=
  pullHom_zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂ _ i _ _ _ rfl rfl _ _

/-- **The descended transition is compatible with pullback**, which is the `pullHom_hom`
condition of the datum being built.  Both sides restrict to the same `…localTransition` over
every member of the base change of `𝒰`, so they agree by `transition_ext`. -/
theorem pullHom_zariskiTransition_eq (a b : S.affineCover.I₀) {V' V : Scheme.{u}} (g : V' ⟶ V)
    (q : V ⟶ S) (q' : V' ⟶ S) (hq : g ≫ q = q')
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q)
    (g₁' : V' ⟶ S.affineCover.X a) (g₂' : V' ⟶ S.affineCover.X b)
    (hgg₁ : g ≫ g₁ = g₁') (hgg₂ : g ≫ g₂ = g₂') :
    pullHom (zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂) g g₁' g₂' hgg₁ hgg₂ =
      zariskiTransition 𝒰 h𝒰 D hT a b q' g₁' g₂'
        (by rw [← hgg₁, Category.assoc, hg₁, hq]) (by rw [← hgg₂, Category.assoc, hg₂, hq]) := by
  have hg₁' : g₁' ≫ S.affineCover.f a = q' := by rw [← hgg₁, Category.assoc, hg₁, hq]
  have hg₂' : g₂' ≫ S.affineCover.f b = q' := by rw [← hgg₂, Category.assoc, hg₂, hq]
  refine transition_ext 𝒰 h𝒰 D a b q' g₁' g₂' fun i ↦ ?_
  rw [pullHom_pullHom (zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂) g g₁' g₂'
      (pullback.fst q' (𝒰.f i)) (pullback.fst q' (𝒰.f i) ≫ g₁')
      (pullback.fst q' (𝒰.f i) ≫ g₂') hgg₁ hgg₂ rfl rfl,
    pullHom_zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂
      (pullback.fst q' (𝒰.f i) ≫ g) i (pullback.snd q' (𝒰.f i))
      (pullback.fst q' (𝒰.f i) ≫ g₁') (pullback.fst q' (𝒰.f i) ≫ g₂')
      (by rw [Category.assoc, hgg₁]) (by rw [Category.assoc, hgg₂])
      (by rw [Category.assoc, hg₁', pullback.condition])
      (by rw [Category.assoc, hg₂', pullback.condition]),
    pullHom_zariskiTransition_fst 𝒰 h𝒰 D hT a b q' g₁' g₂' hg₁' hg₂' i]

/-- **The descended transition at a repeated member of the affine open covering is the
identity**, which is the `hom_self` condition of the datum being built. -/
theorem zariskiTransition_self (a : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g : V ⟶ S.affineCover.X a) (hg : g ≫ S.affineCover.f a = q) :
    zariskiTransition 𝒰 h𝒰 D hT a a q g g hg hg = 𝟙 _ := by
  refine transition_ext 𝒰 h𝒰 D a a q g g fun i ↦ ?_
  rw [pullHom_zariskiTransition_fst 𝒰 h𝒰 D hT a a q g g hg hg i, localTransition_self]
  exact (pullHom_one (pullback.fst q (𝒰.f i)) (pullback.fst q (𝒰.f i) ≫ g) rfl).symm

/-- **The descended transitions compose**, which is the `hom_comp` condition of the datum being
built; over a member of `𝒰` this is `…localTransition_comp`. -/
theorem zariskiTransition_comp (a b d : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b) (g₃ : V ⟶ S.affineCover.X d)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q)
    (hg₃ : g₃ ≫ S.affineCover.f d = q) :
    zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂ ≫
        zariskiTransition 𝒰 h𝒰 D hT b d q g₂ g₃ hg₂ hg₃ =
      zariskiTransition 𝒰 h𝒰 D hT a d q g₁ g₃ hg₁ hg₃ := by
  refine transition_ext 𝒰 h𝒰 D a d q g₁ g₃ fun i ↦ ?_
  rw [pullHom_comp (zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂)
      (zariskiTransition 𝒰 h𝒰 D hT b d q g₂ g₃ hg₂ hg₃) (pullback.fst q (𝒰.f i))
      (pullback.fst q (𝒰.f i) ≫ g₁) (pullback.fst q (𝒰.f i) ≫ g₂)
      (pullback.fst q (𝒰.f i) ≫ g₃) rfl rfl rfl,
    pullHom_zariskiTransition_fst 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂ i,
    pullHom_zariskiTransition_fst 𝒰 h𝒰 D hT b d q g₂ g₃ hg₂ hg₃ i,
    pullHom_zariskiTransition_fst 𝒰 h𝒰 D hT a d q g₁ g₃ hg₁ hg₃ i, localTransition_comp]

/-! ### The datum and the isomorphism -/

/-- **The Zariski descent datum on the affine open covering of the base**, assembled from the
chosen local solutions `…affineOpenModule` and the descended transitions `zariskiTransition`.
Its three conditions are `pullHom_zariskiTransition_eq`, `zariskiTransition_self` and
`zariskiTransition_comp`, and its components are quasi-coherent because the chosen local
solutions are. -/
noncomputable def zariskiDatum : QuasicoherentDescentData (affineZeroHypercover S).f where
  obj :=
    { obj a := (affineOpenModule 𝒰 h𝒰 D a).obj
      hom _ q a₁ a₂ g₁ g₂ hg₁ hg₂ := zariskiTransition 𝒰 h𝒰 D hT a₁ a₂ q g₁ g₂ hg₁ hg₂
      pullHom_hom _ _ g q q' hq a₁ a₂ g₁ g₂ hg₁ hg₂ g₁' g₂' hgg₁ hgg₂ :=
        pullHom_zariskiTransition_eq 𝒰 h𝒰 D hT a₁ a₂ g q q' hq g₁ g₂ hg₁ hg₂ g₁' g₂'
          hgg₁ hgg₂
      hom_self _ q a g hg := zariskiTransition_self 𝒰 h𝒰 D hT a q g hg
      hom_comp _ q a₁ a₂ a₃ g₁ g₂ g₃ hg₁ hg₂ hg₃ :=
        zariskiTransition_comp 𝒰 h𝒰 D hT a₁ a₂ a₃ q g₁ g₂ g₃ hg₁ hg₂ hg₃ }
  property a := (affineOpenModule 𝒰 h𝒰 D a).property

/-- The transitions of `zariskiDatum` are the descended transitions. -/
theorem zariskiDatum_hom (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ (affineZeroHypercover S).f a = q)
    (hg₂ : g₂ ≫ (affineZeroHypercover S).f b = q) :
    (zariskiDatum 𝒰 h𝒰 D hT).obj.hom q g₁ g₂ hg₁ hg₂ =
      zariskiTransition 𝒰 h𝒰 D hT a b q g₁ g₂ hg₁ hg₂ :=
  rfl

/-- **The chosen comparisons intertwine the transitions of `D` with the descended transitions**,
which is the compatibility `hom_comm_of_pullHom_comm` asks for.

Read through `…localComparison_eq`, the left-hand side is a local comparison followed by a
transition of `D`, which is again a local comparison by `…localComparison_comp_hom`; the
right-hand side is the descended transition read off the member `i₂` of `𝒰`, which is a local
comparison followed by an inverse comparison, followed by that same comparison back again. -/
theorem pullHom_affineOpenComponent_comp (a₁ a₂ : S.affineCover.I₀) (i₁ i₂ : 𝒰.I₀)
    {Y : Scheme.{u}} (y : Y ⟶ S)
    (d₁ : Y ⟶ pullback (S.affineCover.f a₁) (𝒰.f i₁))
    (d₂ : Y ⟶ pullback (S.affineCover.f a₂) (𝒰.f i₂))
    (b₁ : Y ⟶ S.affineCover.X a₁) (b₂ : Y ⟶ S.affineCover.X a₂)
    (c₁ : Y ⟶ 𝒰.X i₁) (c₂ : Y ⟶ 𝒰.X i₂)
    (hd₁ : d₁ ≫ pullback.fst (S.affineCover.f a₁) (𝒰.f i₁) = b₁)
    (hd₂ : d₂ ≫ pullback.fst (S.affineCover.f a₂) (𝒰.f i₂) = b₂)
    (he₁ : d₁ ≫ pullback.snd (S.affineCover.f a₁) (𝒰.f i₁) = c₁)
    (he₂ : d₂ ≫ pullback.snd (S.affineCover.f a₂) (𝒰.f i₂) = c₂)
    (hb₁ : b₁ ≫ S.affineCover.f a₁ = y) (hb₂ : b₂ ≫ S.affineCover.f a₂ = y)
    (hc₁ : c₁ ≫ 𝒰.f i₁ = y) (hc₂ : c₂ ≫ 𝒰.f i₂ = y) :
    pullHom (affineOpenComponent 𝒰 h𝒰 D a₁ i₁) d₁ b₁ c₁ hd₁ he₁ ≫ D.obj.hom y c₁ c₂ hc₁ hc₂ =
      zariskiTransition 𝒰 h𝒰 D hT a₁ a₂ y b₁ b₂ hb₁ hb₂ ≫
        pullHom (affineOpenComponent 𝒰 h𝒰 D a₂ i₂) d₂ b₂ c₂ hd₂ he₂ := by
  have hzt : zariskiTransition 𝒰 h𝒰 D hT a₁ a₂ y b₁ b₂ hb₁ hb₂ =
      localTransition 𝒰 h𝒰 D a₁ a₂ b₁ b₂ i₂ c₂ (hb₁.trans hc₂.symm) (hb₂.trans hc₂.symm) :=
    (pullHom_id (zariskiTransition 𝒰 h𝒰 D hT a₁ a₂ y b₁ b₂ hb₁ hb₂)).symm.trans
      (pullHom_zariskiTransition 𝒰 h𝒰 D hT a₁ a₂ y b₁ b₂ hb₁ hb₂ (𝟙 Y) i₂ c₂ b₁ b₂
        (Category.id_comp _) (Category.id_comp _) (hb₁.trans hc₂.symm) (hb₂.trans hc₂.symm))
  rw [← localComparison_eq 𝒰 h𝒰 D a₁ i₁ b₁ c₁ (hb₁.trans hc₁.symm) d₁ hd₁ he₁,
    ← localComparison_eq 𝒰 h𝒰 D a₂ i₂ b₂ c₂ (hb₂.trans hc₂.symm) d₂ hd₂ he₂,
    localComparison_comp_hom 𝒰 h𝒰 D a₁ b₁ y hb₁ i₁ i₂ c₁ c₂ hc₁ hc₂
      (hb₁.trans hc₁.symm) (hb₁.trans hc₂.symm),
    hzt, localTransition_eq_comp, Category.assoc, localComparisonInv_comp, Category.comp_id]

/-- **The restriction of `zariskiDatum` to the affine-open refinement is isomorphic to the
restriction of `D`**, componentwise by the chosen comparisons.

The components need no adjustment: the member of the affine-open refinement above `(a, i)` is
`pullback (U a ⟶ S) (X i ⟶ S)` and the two refinement morphisms are its two projections, so the
two restricted data have components `pullback.fst ^* (M a)` and `pullback.snd ^* (D i)`, between
which `…affineOpenComponent` is exactly an isomorphism.  The compatibility with the transitions
is `hom_comm_of_pullHom_comm`, whose hypothesis says that the comparison at `(a₁, i₁)`, followed
by a transition of `D`, is the transition of `zariskiDatum` followed by the comparison at
`(a₂, i₂)`; read through `…localComparison_eq` that is `…localComparison_comp_hom` on one side and
the definition of `…localTransition` on the other. -/
noncomputable def zariskiDatumIso :
    (pullFunctor (affineOpenRefinementToAffineCover 𝒰 h𝒰)).obj (zariskiDatum 𝒰 h𝒰 D hT) ≅
      (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).obj D := by
  refine ObjectProperty.isoMk _ (Pseudofunctor.DescentData.isoMk
    (fun p ↦ affineOpenComponentIso 𝒰 h𝒰 D p.1 p.2) ?_)
  intro Y y p₁ p₂ d₁ d₂ hd₁ hd₂
  exact hom_comm_of_pullHom_comm (affineOpenRefinementToAffineCover 𝒰 h𝒰)
    (affineOpenRefinementToFamily 𝒰 h𝒰) (zariskiDatum 𝒰 h𝒰 D hT).obj D.obj
    (fun p ↦ affineOpenComponent 𝒰 h𝒰 D p.1 p.2) y d₁ d₂ hd₁ hd₂ y (Category.comp_id y)
    y (Category.comp_id y) _ _ rfl rfl ((Category.assoc _ _ _).trans hd₁)
    ((Category.assoc _ _ _).trans hd₂) _ _ rfl rfl
    (pullbackSnd_comp_f_eq 𝒰 p₁.1 p₁.2 d₁ y ((Category.assoc _ _ _).trans hd₁))
    (pullbackSnd_comp_f_eq 𝒰 p₂.1 p₂.2 d₂ y ((Category.assoc _ _ _).trans hd₂))
    (pullHom_affineOpenComponent_comp 𝒰 h𝒰 D hT p₁.1 p₂.1 p₁.2 p₂.2 y d₁ d₂ _ _ _ _
      rfl rfl rfl rfl ((Category.assoc _ _ _).trans hd₁) ((Category.assoc _ _ _).trans hd₂)
      (pullbackSnd_comp_f_eq 𝒰 p₁.1 p₁.2 d₁ y ((Category.assoc _ _ _).trans hd₁))
      (pullbackSnd_comp_f_eq 𝒰 p₂.1 p₂.2 d₂ y ((Category.assoc _ _ _).trans hd₂)))

end Assembly

/-! ### The target -/

/-- **`…ZariskiDescentDatumOverAffineCover` from the one remaining step.**  Everything the datum
asks for is assembled here: its components are the chosen local solutions, its transitions are
the descended ones, and the isomorphism over the affine-open refinement is the chosen comparison.

By `…zariskiDescentDatumOverAffineCover_iff` the conclusion is the effectivity half of
[Stacks, Tag 023T]; by `…isEffective_fpqcPrecoverage_of_zariskiDatum` it yields that half
directly.  The hypothesis is the gluing of the local transitions along the base change of the
covering family, and nothing else. -/
theorem zariskiDescentDatumOverAffineCover_of_transition
    (hT : ZariskiTransitionOverAnyBase.{v, u}) : ZariskiDescentDatumOverAffineCover.{v, u} :=
  fun 𝒰 h𝒰 D ↦ ⟨zariskiDatum 𝒰 h𝒰 D hT, ⟨zariskiDatumIso 𝒰 h𝒰 D hT⟩⟩

end QuasicoherentDescentData

end AlgebraicGeometry

end
