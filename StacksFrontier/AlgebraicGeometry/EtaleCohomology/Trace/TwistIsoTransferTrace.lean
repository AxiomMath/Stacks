module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance

/-!
# Twisted traces along an isomorphism into an exact direct image

Let `G : C' ⥤ C` be an exact functor preserving injectives, with comparisons `γ : G ⋙ F₁ ≅ F₁'`
and `ρ : P' ⋙ G ⟶ G ⋙ P` compatible with `θ : P ⋙ F₁ ≅ F₁` and `θ' : P' ⋙ F₁' ≅ F₁'`.  If a bounded
below complex `K` with a twist `τ` is isomorphic to `G(K')` for a complex `K'` with a twist `τ'`,
compatibly with `G(τ') ≫ ρ`, the derived twisted endomorphisms of `RF₂(RF₁(K))` and of
`RF₂(RF₁'(K'))` have the same trace.

The second result is the one-object algebra behind Step 8 of the proof of
[Stacks, Tag 03UG]: a base change isomorphism `β : I ⋙ g ≅ g' ⋙ G` which intertwines two twists
`tw`, `tw'` and is compatible with comparisons `S ⋙ I ≅ I`, `S_g ⋙ G ≅ G` also intertwines the
twists `tw ≫ P(g(I(ε)))` and `tw' ≫ P_Z(g'(ε))` built from a map `ε : X ⟶ S X`.

## Main definitions

* `CategoryTheory.Functor.twistedBaseChangeTwist`, `twistedBaseChangeTwistHC`: the twist
  `tw' ≫ P_Z(g'(ε) ≫ aBC) ≫ c` of `g'(X)`, and of `g'(M)` degreewise.

## Main results

* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_iso_map_eq`.
* `CategoryTheory.Functor.twistedBaseChange_compat`.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_twistedBaseChange_eq`.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_iso`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u v u₁ v₁

namespace CategoryTheory.Functor

section IsoInvariance

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

omit [F₁.PreservesInjectiveObjects] in
/-- **The twisted trace is invariant under an isomorphism of complexes intertwining the
twists.**  For `e : K ≅ L` with `τ_K ≫ P(e) = e ≫ τ_L`, the derived twisted endomorphisms of
`RF₂(RF₁(K))` and `RF₂(RF₁(L))` have the same trace. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_iso {K L : CochainComplex.Plus C} (e : K ≅ L)
    (τK : K ⟶ P.mapCochainComplexPlus.obj K) (τL : L ⟶ P.mapCochainComplexPlus.obj L)
    (h : τK ≫ P.mapCochainComplexPlus.map e.hom = e.hom ≫ τL)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hL : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τK)) =
      perfectDerivedTrace R ⟨_, hL⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ L τL)) := by
  refine perfectDerivedTrace_congr R ⟨_, hK⟩ ⟨_, hL⟩ (DerivedCategory.Plus.ι.mapIso
    (F₂.rightDerivedFunctorPlus.mapIso (F₁.rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso e)))) _ _ ?_
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  exact derivedTwistEndo_naturality P F₁ F₂ θ e.hom τK τL (congrArg DerivedCategory.Plus.Q.map h)

end IsoInvariance

section IsoTransfer

variable {R : Type u} [Ring R] {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C']
  [Category.{v₁} D] [Abelian C] [Abelian C'] [Abelian D] [EnoughInjectives C]
  [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R)
  (G : C' ⥤ C) [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)
  (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
    γ.hom.app (P'.obj X) ≫ θ'.hom.app X)

include hθ in
/-- **The twisted trace along an isomorphism `K ≅ G(K')`.**  If `e : K ≅ G(K')` carries the twist
`τ` of `K` to `G(τ') ≫ ρ`, with `G` exact and preserving injectives and `γ`, `ρ` compatible with
`θ`, `θ'`, then the trace of the derived twisted endomorphism of `RF₂(RF₁(K))` attached to `τ` is
that of `RF₂(RF₁'(K'))` attached to `τ'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_iso_map_eq (K : CochainComplex.Plus C)
    (K' : CochainComplex.Plus C') (e : K ≅ G.mapCochainComplexPlus.obj K')
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (τ' : K' ⟶ P'.mapCochainComplexPlus.obj K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K')))))
    (h : τ ≫ P.mapCochainComplexPlus.map e.hom =
      e.hom ≫ G.mapCochainComplexPlus.map τ' ≫ twistTransferMap P P' G ρ K') :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedTrace R ⟨_, hK'⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ' K' τ')) := by
  have hL : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        (G.mapCochainComplexPlus.obj K'))))) :=
    StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
      (F₂.rightDerivedFunctorPlus.mapIso (F₁.rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso e)))).symm hK
  exact (perfectDerivedTrace_derivedTwistEndo_eq_of_iso P F₁ F₂ θ e τ _ h hK hL).trans
    (perfectDerivedTrace_derivedTwistEndo_map_eq P F₁ P' F₁' F₂ G θ θ' γ ρ hθ K' τ' hL hK')

end IsoTransfer

section TwistedBaseChange

variable {A B : Type*} [Category* A] [Category* B] {C C' : Type*} [Category* C] [Category* C']
  (P : C ⥤ C) (P' : C' ⥤ C') (G : C' ⥤ C) (ρ : P' ⋙ G ⟶ G ⋙ P)
  (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C') (PZ : C' ⥤ C') (Sg : C' ⥤ C') (S : A ⥤ A)
  (β : I ⋙ g ≅ g' ⋙ G) (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ PZ) (ρZ : PZ ⋙ G ⟶ G ⋙ P)
  (aBC : S ⋙ g' ⟶ g' ⋙ Sg) (c : Sg ⋙ PZ ≅ P') (cG : Sg ⋙ G ≅ G) (cI : S ⋙ I ≅ I)

/-- **The core compatibility**, for one object: if `β : I ⋙ g ≅ g' ⋙ G` carries `tw` to `tw'`
(through `ρZ`), and is compatible with `aBC`, `cI`, `cG`, and the comparisons `c`, `ρ`, `ρZ`, `cG`
are coherent, then `β` carries the twist `tw ≫ P(g(I(ε) ≫ cI))` of `g(I X)` to the twist
`tw' ≫ PZ(g'(ε) ≫ aBC) ≫ c` of `g' X`. -/
theorem twistedBaseChange_compat (X : A) (εX : X ⟶ S.obj X)
    (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρZ.app (g'.obj X) =
      tw.app (I.obj X) ≫ P.map (β.hom.app X))
    (hpaste : ∀ X, β.hom.app (S.obj X) ≫ G.map (aBC.app X) ≫ cG.hom.app (g'.obj X) =
      g.map (cI.hom.app X) ≫ β.hom.app X)
    (hcoh : ∀ Y, G.map (c.hom.app Y) ≫ ρ.app Y = ρZ.app (Sg.obj Y) ≫ P.map (cG.hom.app Y)) :
    tw.app (I.obj X) ≫ P.map (g.map (I.map εX ≫ cI.hom.app X) ≫ β.hom.app X) =
      β.hom.app X ≫ G.map (tw'.app X ≫ PZ.map (g'.map εX ≫ aBC.app X) ≫
        c.hom.app (g'.obj X)) ≫ ρ.app (g'.obj X) := by
  have hρ := ρZ.naturality (g'.map εX ≫ aBC.app X)
  have hn := β.hom.naturality εX
  dsimp only [Functor.comp_map, Functor.comp_obj] at hρ hn
  simp only [Functor.map_comp, Category.assoc] at hρ ⊢
  have key : g.map (I.map εX) ≫ g.map (cI.hom.app X) ≫ β.hom.app X =
      β.hom.app X ≫ G.map (g'.map εX) ≫ G.map (aBC.app X) ≫ cG.hom.app (g'.obj X) := by
    rw [← hpaste X, reassoc_of% hn]
  rw [hcoh, reassoc_of% hρ, reassoc_of% (hβ X)]
  simp only [← P.map_comp, key]

/-- The twist `tw' ≫ P_Z(g'(ε) ≫ aBC) ≫ c` of `g'(X)` attached to `ε : X ⟶ S(X)`. -/
abbrev twistedBaseChangeTwist (X : A) (εX : X ⟶ S.obj X) : g'.obj X ⟶ P'.obj (g'.obj X) :=
  tw'.app X ≫ PZ.map (g'.map εX ≫ aBC.app X) ≫ c.hom.app (g'.obj X)

/-- **Naturality of `twistedBaseChangeTwist`** in the pair `(X, ε)`. -/
lemma twistedBaseChangeTwist_naturality {X X' : A} (εX : X ⟶ S.obj X) (εX' : X' ⟶ S.obj X')
    (f : X ⟶ X') (hf : f ≫ εX' = εX ≫ S.map f) :
    g'.map f ≫ twistedBaseChangeTwist P' g' PZ Sg S tw' aBC c X' εX' =
      twistedBaseChangeTwist P' g' PZ Sg S tw' aBC c X εX ≫ P'.map (g'.map f) := by
  have h1 := tw'.naturality f
  have h2 := aBC.naturality f
  have h3 := c.hom.naturality (g'.map f)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3
  have key : g'.map f ≫ g'.map εX' ≫ aBC.app X' =
      g'.map εX ≫ aBC.app X ≫ Sg.map (g'.map f) := by
    rw [← g'.map_comp_assoc, hf, g'.map_comp_assoc, h2]
  have key' := congrArg PZ.map key
  simp only [Functor.map_comp] at key'
  simp only [twistedBaseChangeTwist, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% key', h3]

/-- `twistedBaseChange_compat` composed with an isomorphism `L ⟶ I X` intertwining an endomorphism
`δ` of `L` with `I(ε) ≫ cI`. -/
theorem twistedBaseChange_compat_of_hom (X : A) (εX : X ⟶ S.obj X) {Lx : B} (δx : Lx ⟶ Lx)
    (ex : Lx ⟶ I.obj X) (he : δx ≫ ex = ex ≫ I.map εX ≫ cI.hom.app X)
    (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρZ.app (g'.obj X) =
      tw.app (I.obj X) ≫ P.map (β.hom.app X))
    (hpaste : ∀ X, β.hom.app (S.obj X) ≫ G.map (aBC.app X) ≫ cG.hom.app (g'.obj X) =
      g.map (cI.hom.app X) ≫ β.hom.app X)
    (hcoh : ∀ Y, G.map (c.hom.app Y) ≫ ρ.app Y = ρZ.app (Sg.obj Y) ≫ P.map (cG.hom.app Y)) :
    (tw.app Lx ≫ P.map (g.map δx)) ≫ P.map (g.map ex ≫ β.hom.app X) =
      (g.map ex ≫ β.hom.app X) ≫ G.map (tw'.app X ≫ PZ.map (g'.map εX ≫ aBC.app X) ≫
        c.hom.app (g'.obj X)) ≫ ρ.app (g'.obj X) := by
  have hn := tw.naturality ex
  dsimp only [Functor.comp_map] at hn
  have hd : g.map δx ≫ g.map ex = g.map ex ≫ g.map (I.map εX ≫ cI.hom.app X) := by
    rw [← g.map_comp, he, g.map_comp]
  calc (tw.app Lx ≫ P.map (g.map δx)) ≫ P.map (g.map ex ≫ β.hom.app X)
      = tw.app Lx ≫ P.map (g.map δx ≫ g.map ex) ≫ P.map (β.hom.app X) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = g.map ex ≫ tw.app (I.obj X) ≫
          P.map (g.map (I.map εX ≫ cI.hom.app X) ≫ β.hom.app X) := by
        rw [hd, P.map_comp, Category.assoc, reassoc_of% hn, P.map_comp]
    _ = _ := by
        rw [twistedBaseChange_compat P P' G ρ I g g' PZ Sg S β tw tw' ρZ aBC c cG cI X εX hβ
          hpaste hcoh, Category.assoc]

end TwistedBaseChange

section TwistedBaseChangeTrace

variable {R : Type u} [Ring R] {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C'] [Category.{v₁} D] [Abelian C]
  [Abelian C'] [Abelian D] [EnoughInjectives C] [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R)
  (G : C' ⥤ C) (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C') (PZ : C' ⥤ C') (Sg : C' ⥤ C') (S : A ⥤ A)
  [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [I.Additive] [g.Additive] [g'.Additive] [S.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)
  (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
    γ.hom.app (P'.obj X) ≫ θ'.hom.app X)
  (β : I ⋙ g ≅ g' ⋙ G) (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ PZ) (ρZ : PZ ⋙ G ⟶ G ⋙ P)
  (aBC : S ⋙ g' ⟶ g' ⋙ Sg) (c : Sg ⋙ PZ ≅ P') (cG : Sg ⋙ G ≅ G) (cI : S ⋙ I ≅ I)
  (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρZ.app (g'.obj X) =
    tw.app (I.obj X) ≫ P.map (β.hom.app X))
  (hpaste : ∀ X, β.hom.app (S.obj X) ≫ G.map (aBC.app X) ≫ cG.hom.app (g'.obj X) =
    g.map (cI.hom.app X) ≫ β.hom.app X)
  (hcoh : ∀ Y, G.map (c.hom.app Y) ≫ ρ.app Y = ρZ.app (Sg.obj Y) ≫ P.map (cG.hom.app Y))

/-- **The twist of `g'(M)` attached to maps `ε : M^n ⟶ S(M^n)`** commuting with the
differentials, degreewise `tw' ≫ P_Z(g'(ε) ≫ aBC) ≫ c`. -/
def twistedBaseChangeTwistHC (M : CochainComplex A ℤ) (ε : ∀ n, M.X n ⟶ S.obj (M.X n))
    (hε : ∀ i j, M.d i j ≫ ε j = ε i ≫ S.map (M.d i j)) :
    (g'.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶
      (P'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g'.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) where
  f n := twistedBaseChangeTwist P' g' PZ Sg S tw' aBC c (M.X n) (ε n)
  comm' i j _ := (twistedBaseChangeTwist_naturality P' g' PZ Sg S tw' aBC c (ε i) (ε j) (M.d i j)
    (hε i j)).symm

omit [S.Additive] in
include hθ hβ hpaste hcoh in
/-- **The twisted trace along a base change isomorphism, twisted by an endomorphism.** Let
`e : L ≅ I(M)` carry an endomorphism `δ` of `L` to `I(ε) ≫ cI` for maps `ε : M^n ⟶ S(M^n)`.
Then the trace of the derived twisted endomorphism of `RF₂(RF₁(g L))` attached to the twist
`tw ≫ P(g(δ))` is that of `RF₂(RF₁'(g' M))` attached to the twist
`tw' ≫ P_Z(g'(ε) ≫ aBC) ≫ c`. -/
theorem perfectDerivedTrace_derivedTwistEndo_twistedBaseChange_eq
    (L : CochainComplex.Plus B) (δ : L ⟶ L) (M : CochainComplex.Plus A)
    (ε : ∀ n, M.obj.X n ⟶ S.obj (M.obj.X n))
    (e : L ≅ I.mapCochainComplexPlus.obj M)
    (he : ∀ n, δ.hom.f n ≫ e.hom.hom.f n = e.hom.hom.f n ≫ I.map (ε n) ≫ cI.hom.app (M.obj.X n))
    (τ : g.mapCochainComplexPlus.obj L ⟶
      P.mapCochainComplexPlus.obj (g.mapCochainComplexPlus.obj L))
    (hτ : ∀ n, τ.hom.f n = tw.app (L.obj.X n) ≫ P.map (g.map (δ.hom.f n)))
    (hε : ∀ i j, M.obj.d i j ≫ ε j = ε i ≫ S.map (M.obj.d i j))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (g.mapCochainComplexPlus.obj L))))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (g'.mapCochainComplexPlus.obj M)))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map
        (derivedTwistEndo P F₁ F₂ θ (g.mapCochainComplexPlus.obj L) τ)) =
      perfectDerivedTrace R ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map
        (derivedTwistEndo P' F₁' F₂ θ' (g'.mapCochainComplexPlus.obj M)
          (ObjectProperty.homMk (X := g'.mapCochainComplexPlus.obj M)
            (Y := P'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
            (twistedBaseChangeTwistHC P' g' PZ Sg S tw' aBC c M.obj ε hε)))) := by
  let e' : g.mapCochainComplexPlus.obj L ≅
      G.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M) :=
    g.mapCochainComplexPlus.mapIso e ≪≫ baseChangePlusIso G I g g' β M
  refine perfectDerivedTrace_derivedTwistEndo_iso_map_eq P F₁ P' F₁' F₂ G θ θ' γ ρ hθ _ _ e' τ
    _ hK hK' ?_
  ext n : 2
  change τ.hom.f n ≫ P.map (g.map (e.hom.hom.f n) ≫ β.hom.app (M.obj.X n)) =
    (g.map (e.hom.hom.f n) ≫ β.hom.app (M.obj.X n)) ≫
      G.map (twistedBaseChangeTwist P' g' PZ Sg S tw' aBC c (M.obj.X n) (ε n)) ≫
      ρ.app (g'.obj (M.obj.X n))
  rw [hτ]
  exact twistedBaseChange_compat_of_hom P P' G ρ I g g' PZ Sg S β tw tw' ρZ aBC c cG cI
    (M.obj.X n) (ε n) (δ.hom.f n) (e.hom.hom.f n) (he n) hβ hpaste hcoh

end TwistedBaseChangeTrace

end CategoryTheory.Functor

end
