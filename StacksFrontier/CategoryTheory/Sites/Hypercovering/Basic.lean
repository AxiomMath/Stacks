module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.Pretopology
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence

/-!
# Hypercoverings of an object of a site

Let `C` be a site given by a pretopology `J`, and assume `C` has fibre products. The category
of *semi-representable objects over* `X : C` — written `SR(C, X)` in the source — is the
category `FormalCoproduct (Over X)` of indexed families of objects over `X`. This file defines
when a morphism of `SR(C, X)` is *covering*, defines a *hypercovering of `X`* as a simplicial
object of `SR(C, X)` whose degree-zero term covers `X` and whose canonical map to each
successive coskeleton is covering, and proves the stability of coverings under composition
with an isomorphism and under a functor which takes covering families to covering families.

## Main definitions

* `IsCovering` and `IsCoveringOver`: a morphism of formal coproducts, respectively of formal
  coproducts of objects over `X`, is covering when its family of components over each index of
  the target is a covering family of the site (Tag 01G3).
* `IsHypercovering`: the predicate that a simplicial object of `SR(C, X)` is a hypercovering
  of `X` (Tag 01G5).
* `mapFormalCoproduct`: the functor on formal coproducts induced by a functor, applying it to
  every component.
* `MapsCoveringsToCoverings`: the covering clause of the definition of a continuous functor
  (Tag 00WV): the image family of a covering family is a covering family.

## Main results

* `hasPointwiseRightKanExtension_formalCoproductOver`: the coskeleta of simplicial objects of
  `SR(C, X)` all exist.
* `IsCovering.comp_isIso` and `IsCoveringOver.comp_isIso`: composing a covering morphism with
  an isomorphism gives a covering morphism.
* `IsCoveringOver.map`: a functor taking covering families to covering families carries
  covering morphisms of `SR(D, Y)` to covering morphisms of `SR(C, u Y)`.
* `isTerminal_mapFormalCoproduct_terminal`: the image of the terminal object of `SR(D, Y)`
  under `mapFormalCoproduct (Over.post u)` is terminal.
* `IsHypercovering.map_zero`: the degree-zero clause of Tag 0DAZ — the image of a
  hypercovering covers the image of the base object.

## Implementation notes

`IsCovering` and `IsCoveringOver` are abbreviations, written out in the explicit form in which
their two clauses are used, rather than through `mapFormalCoproduct (Over.forget X)`;
`isCoveringOver_iff_isCovering` records that the second is the first applied to the underlying
morphism in `C`, and is true by definition.

Coverings of a pretopology are *not* downward closed, which is the reason for the covering
clause `MapsCoveringsToCoverings` stated here. Tag 00WV asks that the image family
`{u Vᵢ → u V}` of a covering family be a covering family; the weaker-looking condition that
the presieve `Presieve.functorPushforward u S` be a covering is a genuinely different
requirement, because that presieve also contains every arrow factoring through a member of the
image family, and a pretopology may contain one of the two presieves and not the other. Only
the image-family form implies that coverings of `SR(D, Y)` map to coverings of `SR(C, u Y)`.

The index universe `w` of the formal coproducts is independent of the universes of `C` and `D`,
and `MapsCoveringsToCoverings` is stated for `w`-indexed covering families, which is exactly
what the covering clauses of `SR(C, X)` produce.

## References

* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂ v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

section Presieve

variable {C : Type u} [Category.{v} C]

/-- Reindexing a family of arrows along a bijection does not change the presieve it generates. -/
theorem ofArrows_reindex {X : C} {ι ι' : Type*} (e : ι' ≃ ι) (A : ι → C)
    (g : ∀ i, A i ⟶ X) :
    Presieve.ofArrows (fun i ↦ A (e i)) (fun i ↦ g (e i)) = Presieve.ofArrows A g := by
  funext Z
  ext k
  constructor
  · rintro ⟨i⟩
    exact Presieve.ofArrows.mk (e i)
  · rintro ⟨i⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact Presieve.ofArrows.mk j

/-- Two families of arrows indexed by subtypes cut out by equivalent predicates, whose
members agree, generate the same presieve. -/
theorem ofArrows_subtype_congr {X : C} {ι : Type*} {p q : ι → Prop} (h : ∀ i, p i ↔ q i)
    (A : ι → C) (gp : ∀ i : { i // p i }, A i.1 ⟶ X) (gq : ∀ i : { i // q i }, A i.1 ⟶ X)
    (hg : ∀ (i : ι) (hp : p i) (hq : q i), gp ⟨i, hp⟩ = gq ⟨i, hq⟩) :
    Presieve.ofArrows (fun i : { i // p i } ↦ A i.1) gp =
      Presieve.ofArrows (fun i : { i // q i } ↦ A i.1) gq := by
  funext W
  ext k
  constructor
  · rintro ⟨⟨i, hi⟩⟩
    rw [hg i hi ((h i).1 hi)]
    exact Presieve.ofArrows.mk (Y := fun i : { i // q i } ↦ A i.1) (f := gq)
      ⟨i, (h i).1 hi⟩
  · rintro ⟨⟨i, hi⟩⟩
    rw [← hg i ((h i).2 hi) hi]
    exact Presieve.ofArrows.mk (Y := fun i : { i // p i } ↦ A i.1) (f := gp)
      ⟨i, (h i).2 hi⟩

variable [HasPullbacks C] (J : Pretopology C)

/-- A covering family stays covering after composing every member with a fixed isomorphism
of the target. -/
theorem mem_coverings_comp_isIso {X Y : C} {ι : Type*} (A : ι → C) (g : ∀ i, A i ⟶ X)
    (hg : Presieve.ofArrows A g ∈ J X) (h : X ⟶ Y) [IsIso h] :
    Presieve.ofArrows A (fun i ↦ g i ≫ h) ∈ J Y := by
  set R : Presieve Y := Presieve.ofArrows A (fun i ↦ g i ≫ h) with hRdef
  set S : Presieve Y := Presieve.ofArrows (fun _ : PUnit.{1} ↦ X) (fun _ ↦ h) with hSdef
  set T : ∀ ⦃Z : C⦄ (f : Z ⟶ Y), S f → Presieve Z :=
    fun _ f _ _ k ↦ R (k ≫ f) with hTdef
  have hbind : S.bind T = R := by
    funext W
    ext f₀
    constructor
    · rintro ⟨Z, g', f', H, hT, rfl⟩
      exact hT
    · rintro ⟨i⟩
      exact Presieve.bind_comp h (Presieve.ofArrows.mk PUnit.unit) (Presieve.ofArrows.mk i)
  rw [← hbind]
  refine J.transitive S T (by rw [hSdef, Presieve.ofArrows_pUnit]; exact J.has_isos h) ?_
  rintro Z f ⟨i⟩
  convert hg using 1
  funext W
  ext k
  constructor
  · intro hk
    obtain ⟨i', he, hk'⟩ := Presieve.ofArrows_surj _ _ hk
    refine Presieve.ofArrows.mk' i' he.symm ((cancel_mono h).mp ?_)
    simpa using hk'
  · rintro ⟨i'⟩
    exact Presieve.ofArrows.mk i'

end Presieve

section FormalCoproduct

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The functor on formal coproducts obtained by applying a functor to every component. -/
@[simps!]
def mapFormalCoproduct (u : D ⥤ C) : FormalCoproduct.{w} D ⥤ FormalCoproduct.{w} C where
  obj X := ⟨X.I, fun i ↦ u.obj (X.obj i)⟩
  map f := ⟨f.f, fun i ↦ u.map (f.φ i)⟩
  map_id X := by
    ext
    · rfl
    · simp
  map_comp f g := by
    ext
    · rfl
    · simp

/-- The index map of an isomorphism of formal coproducts is a bijection, with inverse the
index map of the inverse isomorphism. -/
theorem inv_f_f {U V : FormalCoproduct.{w} C} (e : U ⟶ V) [IsIso e] (i : U.I) :
    (inv e).f (e.f i) = i :=
  congrFun (congrArg FormalCoproduct.Hom.f (IsIso.hom_inv_id e)) i

/-- The index map of an isomorphism of formal coproducts is a bijection, with inverse the
index map of the inverse isomorphism. -/
theorem f_inv_f {U V : FormalCoproduct.{w} C} (e : U ⟶ V) [IsIso e] (j : V.I) :
    e.f ((inv e).f j) = j :=
  congrFun (congrArg FormalCoproduct.Hom.f (IsIso.inv_hom_id e)) j

/-- The components of an isomorphism of formal coproducts are isomorphisms. -/
instance isIso_φ {U V : FormalCoproduct.{w} C} (e : U ⟶ V) [IsIso e] (i : U.I) :
    IsIso (e.φ i) := by
  obtain ⟨h₁, h₂⟩ := (FormalCoproduct.hom_ext_iff (e ≫ inv e) (𝟙 U)).1 (IsIso.hom_inv_id e)
  obtain ⟨h₃, h₄⟩ := (FormalCoproduct.hom_ext_iff (inv e ≫ e) (𝟙 V)).1 (IsIso.inv_hom_id e)
  have hU : U.obj ((inv e).f (e.f i)) = U.obj i := congrArg U.obj (inv_f_f e i)
  have hsec : e.φ i ≫ (inv e).φ (e.f i) ≫ eqToHom hU = 𝟙 (U.obj i) := by
    simpa using h₂ i
  have hret : ((inv e).φ (e.f i) ≫ eqToHom hU) ≫ eqToHom hU.symm ≫
      e.φ ((inv e).f (e.f i)) ≫ eqToHom (congrArg V.obj (f_inv_f e (e.f i))) =
      𝟙 (V.obj (e.f i)) := by
    simpa using h₄ (e.f i)
  have hse : IsSplitEpi ((inv e).φ (e.f i) ≫ eqToHom hU) := ⟨⟨⟨e.φ i, by simpa using hsec⟩⟩⟩
  have hsm : IsSplitMono ((inv e).φ (e.f i) ≫ eqToHom hU) := ⟨⟨⟨_, hret⟩⟩⟩
  have : IsIso ((inv e).φ (e.f i) ≫ eqToHom hU) :=
    isIso_of_mono_of_isSplitEpi _
  exact IsIso.of_isIso_fac_right hsec

/-- Factoring the component of a composite over an index of the final target through the
component of the first map over the intermediate index. -/
theorem comp_φ_eqToHom {U V V' : FormalCoproduct.{w} C} (f : U ⟶ V) (e : V ⟶ V')
    {i : U.I} {j : V.I} {j' : V'.I} (hi : f.f i = j) (he : e.f j = j')
    (h₁ : (f ≫ e).f i = j') :
    (f ≫ e).φ i ≫ eqToHom (congrArg V'.obj h₁) =
      (f.φ i ≫ eqToHom (congrArg V.obj hi)) ≫ e.φ j ≫ eqToHom (congrArg V'.obj he) := by
  subst hi
  simp

end FormalCoproduct

section Covering

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  {D : Type u₂} [Category.{v₂} D] [HasPullbacks D]

/-- A morphism of formal coproducts is covering if, over every target component, its component
morphisms form a covering family for the given pretopology. -/
abbrev IsCovering (J : Pretopology C) {U V : FormalCoproduct.{w} C} (f : U ⟶ V) : Prop :=
  ∀ j : V.I,
    Presieve.ofArrows
      (fun i : { i : U.I // f.f i = j } ↦ U.obj i.1)
      (fun i ↦ f.φ i.1 ≫ eqToHom (congrArg V.obj i.2)) ∈ J (V.obj j)

/-- A morphism of formal coproducts of objects over `X` is covering if its underlying component
morphisms in `C` form a covering morphism of formal coproducts. -/
abbrev IsCoveringOver (J : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) : Prop :=
  ∀ j : V.I,
    Presieve.ofArrows
      (fun i : { i : U.I // f.f i = j } ↦ (U.obj i.1).left)
      (fun i ↦ (f.φ i.1).left ≫
        eqToHom (congrArg (fun k ↦ (V.obj k).left) i.2)) ∈ J (V.obj j).left

/-- Being covering over `X` is being covering after forgetting down to `C`. -/
theorem isCoveringOver_iff_isCovering (J : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) :
    IsCoveringOver J f ↔
      IsCovering J ((mapFormalCoproduct (Over.forget X)).map f) :=
  Iff.rfl

/-- A covering morphism of formal coproducts stays covering after composing with an
isomorphism. -/
theorem IsCovering.comp_isIso (J : Pretopology C) {U V V' : FormalCoproduct.{w} C}
    {f : U ⟶ V} (hf : IsCovering J f) (e : V ⟶ V') [IsIso e] :
    IsCovering J (f ≫ e) := by
  intro j'
  set j : V.I := (inv e).f j' with hj
  have he : e.f j = j' := f_inv_f e j'
  have hiff : ∀ i : U.I, (f ≫ e).f i = j' ↔ f.f i = j := fun i ↦ by
    constructor
    · intro h
      rw [hj, ← h]
      exact (inv_f_f e _).symm
    · intro h
      rw [show (f ≫ e).f i = e.f (f.f i) from rfl, h, he]
  rw [ofArrows_subtype_congr hiff U.obj
    (fun i ↦ (f ≫ e).φ i.1 ≫ eqToHom (congrArg V'.obj i.2))
    (fun i ↦ (f.φ i.1 ≫ eqToHom (congrArg V.obj i.2)) ≫
      e.φ j ≫ eqToHom (congrArg V'.obj he))
    (fun i hp hq ↦ comp_φ_eqToHom f e hq he hp)]
  exact mem_coverings_comp_isIso J _ _ (hf j) _

/-- A covering morphism of formal coproducts of objects over `X` stays covering after
composing with an isomorphism. -/
theorem IsCoveringOver.comp_isIso (J : Pretopology C) {X : C}
    {U V V' : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} (hf : IsCoveringOver J f)
    (e : V ⟶ V') [IsIso e] :
    IsCoveringOver J (f ≫ e) := by
  rw [isCoveringOver_iff_isCovering] at hf ⊢
  rw [Functor.map_comp]
  exact hf.comp_isIso J _

/-- A morphism is covering as soon as it is covering after composing with an isomorphism. This
is the converse of `IsCoveringOver.comp_isIso`. -/
theorem IsCoveringOver.of_comp_isIso (J : Pretopology C) {X : C}
    {U V V' : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} (e : V ⟶ V') [IsIso e]
    (h : IsCoveringOver J (f ≫ e)) :
    IsCoveringOver J f := by
  simpa using h.comp_isIso J (inv e)

/-- Composing with an isomorphism does not change whether a morphism is covering. -/
theorem isCoveringOver_comp_iso_iff (J : Pretopology C) {X : C}
    {A B D : FormalCoproduct.{w} (Over X)} (f : A ⟶ B) (e : B ≅ D) :
    IsCoveringOver J (f ≫ e.hom) ↔ IsCoveringOver J f :=
  ⟨fun h ↦ IsCoveringOver.of_comp_isIso J e.hom h, fun h ↦ h.comp_isIso J e.hom⟩

/-- A morphism of formal coproducts over `X` between one-summand objects is covering exactly when
its single component generates a covering presieve. -/
theorem isCoveringOver_unique_iff_singleton {X : C}
    {A B : FormalCoproduct.{w} (Over X)} (J : Pretopology C) [Unique A.I]
    [Unique B.I] (f : A ⟶ B) (j : B.I) :
    IsCoveringOver J f ↔
      Presieve.singleton ((f.φ default).left ≫
        eqToHom (congrArg (fun k ↦ (B.obj k).left)
          (Subsingleton.elim (f.f default) j))) ∈ J (B.obj j).left := by
  constructor
  · intro hf
    have h := hf j
    let : Unique { i : A.I // f.f i = j } :=
      ⟨⟨default, Subsingleton.elim _ _⟩, fun i ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Presieve.ofArrows_of_unique] at h
    change Presieve.singleton ((f.φ default).left ≫
      eqToHom (congrArg (fun k ↦ (B.obj k).left) (Subsingleton.elim _ j))) ∈
      J (B.obj j).left at h
    convert h using 1
  · intro h k
    let : Unique { i : A.I // f.f i = k } :=
      ⟨⟨default, Subsingleton.elim _ _⟩, fun i ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    have hkj : k = j := Subsingleton.elim _ _
    subst k
    rw [Presieve.ofArrows_of_unique]
    show Presieve.singleton ((f.φ default).left ≫
      eqToHom (congrArg (fun k ↦ (B.obj k).left) (Subsingleton.elim _ j))) ∈
      J (B.obj j).left
    convert h using 1

/-- A functor between sites given by pretopologies takes covering families to covering
families. -/
def MapsCoveringsToCoverings (u : D ⥤ C) (JD : Pretopology D) (JC : Pretopology C) : Prop :=
  ∀ ⦃V : D⦄ {ι : Type w} (A : ι → D) (g : ∀ i, A i ⟶ V),
    Presieve.ofArrows A g ∈ JD V →
      Presieve.ofArrows (fun i ↦ u.obj (A i)) (fun i ↦ u.map (g i)) ∈ JC (u.obj V)

/-- A functor taking coverings to coverings takes covering morphisms of semi-representable
objects over `Y` to covering morphisms over the image of `Y`. -/
theorem IsCoveringOver.map {u : D ⥤ C} {JD : Pretopology D} {JC : Pretopology C}
    (hu : MapsCoveringsToCoverings.{w} u JD JC) {Y : D}
    {U V : FormalCoproduct.{w} (Over Y)} {f : U ⟶ V} (hf : IsCoveringOver JD f) :
    IsCoveringOver JC ((mapFormalCoproduct (Over.post u)).map f) := by
  intro j
  have harr : (fun i : { i : U.I // f.f i = j } ↦
        u.map ((f.φ i.1).left ≫ eqToHom (congrArg (fun k ↦ (V.obj k).left) i.2))) =
      fun i : { i : U.I // f.f i = j } ↦ u.map (f.φ i.1).left ≫
        eqToHom (congrArg (fun k ↦ u.obj (V.obj k).left) i.2) := by
    funext i
    rw [u.map_comp, eqToHom_map]
  exact harr ▸ hu _ _ (hf j)

end Covering

section Hypercovering

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]

/-- The pointwise right Kan extensions defining all coskeleta of simplicial formal coproducts
over an object exist when the underlying category has pullbacks. -/
instance hasPointwiseRightKanExtension_formalCoproductOver {X : C} (n : ℕ)
    (F : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) n) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F := by
  let _ : HasFiniteLimits (FormalCoproduct.{w} (Over X)) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let h :=
    hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
      (C := FormalCoproduct.{w} (Over X))
  rcases n with _ | n
  · exact h.1 (by infer_instance) F
  · exact h.2 (fun _ _ _ _ ↦ by infer_instance) (n + 1) (by omega) F

/-- A hypercovering of `X` for the pretopology `J`: its family in degree zero covers `X`, and in
every following degree its canonical map to the matching object given by the preceding
coskeleton is covering. -/
abbrev IsHypercovering (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) : Prop :=
  IsCoveringOver J (terminal.from (K.obj (op ⦋0⦌))) ∧
    ∀ n : ℕ, IsCoveringOver J
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌))

end Hypercovering

section Map

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  {D : Type u₂} [Category.{v₂} D] [HasPullbacks D]
  (u : D ⥤ C) (Y : D)

/-- The image of the terminal semi-representable object over `Y` is terminal. -/
noncomputable def isTerminal_mapFormalCoproduct_terminal :
    IsTerminal ((mapFormalCoproduct.{w} (Over.post u)).obj
      (⊤_ (FormalCoproduct.{w} (Over Y)))) := by
  have hT : IsTerminal (Over.mk (u.map (𝟙 Y))) := by
    rw [CategoryTheory.Functor.map_id]
    exact Over.mkIdTerminal
  refine IsTerminal.ofIso
    (FormalCoproduct.isTerminalIncl ((Over.post u).obj (Over.mk (𝟙 Y))) hT) ?_
  exact ((mapFormalCoproduct (Over.post u)).mapIso
    (terminalIsTerminal.uniqueUpToIso
      (FormalCoproduct.isTerminalIncl (Over.mk (𝟙 Y)) Over.mkIdTerminal))).symm

/-- The canonical morphism from the image of the terminal object to the terminal object is an
isomorphism. -/
instance isIso_terminalFrom_mapFormalCoproduct_terminal :
    IsIso (terminal.from
      ((mapFormalCoproduct.{w} (Over.post u)).obj (⊤_ (FormalCoproduct.{w} (Over Y))))) := by
  have hT := isTerminal_mapFormalCoproduct_terminal.{w} u Y
  exact ⟨hT.from _, hT.hom_ext _ _, terminal.hom_ext _ _⟩

/-- If the degree-zero term of a simplicial semi-representable object over `Y` covers `Y`, then
its image under a functor taking coverings to coverings covers the image of `Y`. -/
theorem IsHypercovering.map_zero {JD : Pretopology D} {JC : Pretopology C}
    (hu : MapsCoveringsToCoverings.{w} u JD JC)
    {Z : FormalCoproduct.{w} (Over Y)} (hZ : IsCoveringOver JD (terminal.from Z)) :
    IsCoveringOver JC
      (terminal.from ((mapFormalCoproduct.{w} (Over.post u)).obj Z)) := by
  have hfac : terminal.from ((mapFormalCoproduct.{w} (Over.post u)).obj Z) =
      (mapFormalCoproduct.{w} (Over.post u)).map (terminal.from Z) ≫
        terminal.from ((mapFormalCoproduct.{w} (Over.post u)).obj
          (⊤_ (FormalCoproduct.{w} (Over Y)))) :=
    terminal.hom_ext _ _
  rw [hfac]
  exact (hZ.map hu).comp_isIso JC _

end Map



end Stacks.CategoryTheory.Hypercovering

end
