module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.Transfer

/-!
# Taking disjoint unions in a hypercovering

Let `X` be an object of a site with fibre products. If the coproducts occurring in a
hypercovering of `X` exist, taking those coproducts commutes with the finite limits used to form
the matching objects, and the resulting maps preserve coverings, then taking coproducts
degreewise again produces a hypercovering of `X`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.SummableFormalCoproduct` is the full subcategory of formal
  coproducts whose indicated coproduct exists.
* `Stacks.CategoryTheory.Hypercovering.takeCoproduct` takes the coproduct of such a family.
* `Stacks.CategoryTheory.Hypercovering.takeUnions` regards that coproduct as a singleton formal
  coproduct.
* `Stacks.CategoryTheory.Hypercovering.takeUnionsSimplicial` takes coproducts degreewise in a
  simplicial object whose terms admit them.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isHypercovering_whiskerLift` is the construction for an
  arbitrary property of semi-representable objects and an arbitrary functor out of the full
  subcategory it cuts out.
* `Stacks.CategoryTheory.Hypercovering.isHypercovering_takeUnionsSimplicial` says that taking
  disjoint unions degreewise preserves hypercoverings under the finite-limit and
  covering-preservation hypotheses.

## Implementation notes

Membership in the full subcategory `SummableFormalCoproduct` asks only that the displayed family
have a coproduct. The hypotheses are that this property is closed under finite limits, that
`takeUnions` preserves those limits and sends coverings to coverings, and that each term of the
simplicial formal coproduct `K` has a coproduct; `K` is not assumed to lift to the subcategory.

## References

* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Simplicial SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-- Formal coproducts for which the corresponding coproduct in `C` exists. -/
abbrev SummableFormalCoproduct (C : Type u) [Category.{v} C] :=
  ObjectProperty.FullSubcategory
    (fun U : FormalCoproduct.{w} C ↦ HasCoproduct U.obj)

/-- The inclusion of summable formal coproducts into all formal coproducts. -/
abbrev summableInclusion :
    SummableFormalCoproduct.{w} C ⥤ FormalCoproduct.{w} C :=
  ObjectProperty.ι (fun U : FormalCoproduct.{w} C ↦ HasCoproduct U.obj)

/-- Take the coproduct represented by a summable formal coproduct. -/
noncomputable def takeCoproduct : SummableFormalCoproduct.{w} C ⥤ C where
  obj U := by
    let := U.property
    exact ∐ U.obj.obj
  map {U V} f := by
    let := U.property
    let := V.property
    exact Sigma.map' f.hom.f f.hom.φ
  map_id U := by
    let := U.property
    exact Sigma.map'_id_id
  map_comp {U V W} f g := by
    let := U.property
    let := V.property
    let := W.property
    exact (Sigma.map'_comp_map' g.hom.f f.hom.f g.hom.φ f.hom.φ).symm

/-- Take a summable formal coproduct and regard its coproduct as a singleton formal coproduct. -/
noncomputable def takeUnions :
    SummableFormalCoproduct.{w} C ⥤ FormalCoproduct.{w} C :=
  takeCoproduct (C := C) ⋙ FormalCoproduct.incl C

variable [HasPullbacks C] (J : Pretopology C) {X : C}

/-- Take the disjoint unions in each degree of a simplicial formal coproduct over `X`.
Only the coproducts of its actual terms are required to exist. -/
@[stacks 0DB2 "the degreewise construction"]
noncomputable def takeUnionsSimplicial
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hsum : ∀ n, HasCoproduct (K.obj n).obj) :
    SimplicialObject (FormalCoproduct.{w} (Over X)) :=
  (((SimplicialObject.whiskering _ _).obj (takeUnions (C := Over X))).obj
    ((ObjectProperty.lift
      (fun U : FormalCoproduct.{w} (Over X) ↦ HasCoproduct U.obj) K hsum)))

/-- Let `P` be a property of semi-representable objects over `X` and `G` a functor out of the
full subcategory it cuts out. If `P` is closed under finite limits, `G` preserves them, and `G`
sends coverings to coverings, then whiskering with `G` a hypercovering whose terms satisfy `P`
again gives a hypercovering. -/
lemma isHypercovering_whiskerLift (P : ObjectProperty (FormalCoproduct.{w} (Over X)))
    [P.IsClosedUnderFiniteLimits]
    (G : P.FullSubcategory ⥤ FormalCoproduct.{w} (Over X)) [PreservesFiniteLimits G]
    (hcover : ∀ ⦃U V : P.FullSubcategory⦄ (f : U ⟶ V),
      IsCoveringOver J (P.ι.map f) → IsCoveringOver J (G.map f))
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hsum : ∀ n, P (K.obj n))
    (hK : IsHypercovering J K) :
    IsHypercovering J (((SimplicialObject.whiskering _ _).obj G).obj (P.lift K hsum)) := by
  dsimp [IsHypercovering] at hK ⊢
  rcases hK with ⟨h0, hn⟩
  let H := P.lift K hsum
  let : HasFiniteLimits (FormalCoproduct.{w} (Over X)) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : HasFiniteLimits P.FullSubcategory := inferInstance
  constructor
  · have htop : P (⊤_ (FormalCoproduct.{w} (Over X))) :=
      P.prop_of_isLimit (F := Functor.empty (FormalCoproduct.{w} (Over X)))
        (c := limit.cone (Functor.empty (FormalCoproduct.{w} (Over X))))
        (limit.isLimit _) (by intro j; cases j.as)
    let V : P.FullSubcategory := ⟨⊤_ (FormalCoproduct.{w} (Over X)), htop⟩
    have hV : IsTerminal V := by
      apply IsTerminal.ofUniqueHom
        (fun W ↦ ObjectProperty.homMk (P := P)
          (terminal.from (C := FormalCoproduct.{w} (Over X)) W.1))
      intro W f
      apply ObjectProperty.hom_ext
      exact terminal.hom_ext _ _
    let c : Cone (Functor.empty P.FullSubcategory) := asEmptyCone V
    have hc : IsLimit c :=
      (isLimitEquivIsTerminalOfIsEmpty (P.FullSubcategory) c).symm hV
    let : PreservesLimit (Functor.empty P.FullSubcategory) G := by infer_instance
    have hc' : IsLimit (G.mapCone c) := isLimitOfPreserves G hc
    have hGV : IsTerminal (G.obj V) :=
      isLimitEquivIsTerminalOfIsEmpty (FormalCoproduct.{w} (Over X)) (G.mapCone c) hc'
    have hterminal : IsIso (terminal.from (G.obj V)) :=
      isIso_of_isTerminal hGV terminalIsTerminal _
    let e : G.obj V ≅ ⊤_ (FormalCoproduct.{w} (Over X)) := asIso (terminal.from (G.obj V))
    let f : H.obj (Opposite.op ⦋0⦌) ⟶ V :=
      ObjectProperty.homMk (P := P) (terminal.from (K.obj (Opposite.op ⦋0⦌)))
    have h0' : IsCoveringOver J (P.ι.map f) := by
      simpa [H, f, V] using h0
    have h0'' := hcover f h0'
    have hcomp : G.map f ≫ e.hom = terminal.from (G.obj (H.obj (Opposite.op ⦋0⦌))) :=
      terminal.hom_ext _ _
    have h0''' := h0''.comp_isIso J e.hom
    rw [hcomp] at h0'''
    simpa [H] using h0'''
  · intro n
    let L := (SimplexCategory.Truncated.inclusion n).op
    let F := (SimplicialObject.truncation n).obj H
    let : ∀ (F : SimplicialObject.Truncated P.FullSubcategory n),
        L.HasPointwiseRightKanExtension F := by
      intro F
      let h := hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := P.FullSubcategory)
      rcases n with _ | n
      · exact h.1 (by infer_instance) F
      · exact h.2 (fun _ _ _ _ ↦ by infer_instance) (n + 1) (by omega) F
    let : ∀ (Y : SimplexCategoryᵒᵖ),
        FinCategory (StructuredArrow Y (SimplexCategory.Truncated.inclusion n).op) :=
      fun Y ↦ Construction.finCategoryTruncatedStructuredArrow n Y
    let : Functor.PreservesPointwiseRightKanExtension G F L := by
      intro Y
      let : PreservesLimit (StructuredArrow.proj Y L ⋙ F) G := by infer_instance
      infer_instance
    let : L.HasPointwiseRightKanExtension (F ⋙ G) := by infer_instance
    let : Functor.PreservesRightKanExtension G F L := by infer_instance
    let f := ((SimplicialObject.coskAdj n).unit.app H).app (Opposite.op ⦋n + 1⦌)
    let I := P.ι
    have hHI : H ⋙ I = K := rfl
    let E : H ⋙ I ≅ K := eqToIso hHI
    let : ∀ (F : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) n),
        L.HasPointwiseRightKanExtension F := by infer_instance
    let : Functor.PreservesPointwiseRightKanExtension I F L := by
      intro Y
      let : PreservesLimit (StructuredArrow.proj Y L ⋙ F) I := by infer_instance
      infer_instance
    let : Functor.PreservesRightKanExtension I F L := by infer_instance
    have key : ∀ (Φ : P.FullSubcategory ⥤ FormalCoproduct.{w} (Over X))
        [Φ.PreservesRightKanExtension (L ⋙ H) L],
        ∃ e : Φ.obj (((SimplicialObject.Truncated.cosk n).obj F).obj (Opposite.op ⦋n + 1⦌)) ≅
          ((SimplicialObject.Truncated.cosk n).obj
            ((SimplicialObject.truncation n).obj (H ⋙ Φ))).obj (Opposite.op ⦋n + 1⦌),
        Φ.map f ≫ e.hom =
          ((SimplicialObject.coskAdj n).unit.app (H ⋙ Φ)).app (Opposite.op ⦋n + 1⦌) :=
      fun Φ _ ↦ ⟨((Φ.rightKanExtensionCompIsoOfPreserves (L ⋙ H) L).app _).trans
        (((L.ran).mapIso (Functor.associator L H Φ)).app _),
        congrArg (fun η ↦ η.app (Opposite.op ⦋n + 1⦌))
          (Construction.ranAdjunction_unit_whiskerRight L H Φ)⟩
    let fK := ((SimplicialObject.coskAdj n).unit.app K).app (Opposite.op ⦋n + 1⦌)
    let eK : (SimplicialObject.Truncated.cosk n).obj
        ((SimplicialObject.truncation n).obj (H ⋙ I)) ≅
        (SimplicialObject.Truncated.cosk n).obj
          ((SimplicialObject.truncation n).obj K) := Iso.refl _
    have hunitK :
        ((SimplicialObject.coskAdj n).unit.app (H ⋙ I)).app
            (Opposite.op ⦋n + 1⦌) ≫ (eK.app (Opposite.op ⦋n + 1⦌)).hom = fK := by
      have hnat := congrArg (fun α ↦ α.app (Opposite.op ⦋n + 1⦌))
        ((L.ranAdjunction (FormalCoproduct (Over X))).unit.naturality E.hom)
      simpa [E, eK, hHI, fK, SimplicialObject.coskAdj,
        SimplicialObject.truncation] using hnat.symm
    have hfn : IsCoveringOver J (P.ι.map f) := by
      have hA : IsCoveringOver J fK := hn n
      rw [← hunitK] at hA
      have hA' := IsCoveringOver.of_comp_isIso J (eK.app (Opposite.op ⦋n + 1⦌)).hom hA
      obtain ⟨eI, hI⟩ := key I
      rw [← hI] at hA'
      exact IsCoveringOver.of_comp_isIso J eI.hom hA'
    have hGf := hcover f hfn
    obtain ⟨eG, hunitG⟩ := key G
    have hfinal := hGf.comp_isIso J eG.hom
    rw [hunitG] at hfinal
    simpa [H, SimplicialObject.coskAdj, SimplicialObject.truncation] using hfinal

/-- If summable semi-representable objects over `X` are closed
under finite limits, taking their coproducts commutes with those limits, and it sends coverings
to coverings, then applying it degreewise to a hypercovering again gives a hypercovering. -/
@[stacks 0DB2 "preservation of hypercoverings"]
lemma isHypercovering_takeUnionsSimplicial
    [ObjectProperty.IsClosedUnderFiniteLimits
      (fun U : FormalCoproduct.{w} (Over X) ↦ HasCoproduct U.obj)]
    [PreservesFiniteLimits (takeUnions.{w, v, max u v} (C := Over X))]
    (hcover : ∀ ⦃U V : SummableFormalCoproduct.{w} (Over X)⦄ (f : U ⟶ V),
      IsCoveringOver J ((summableInclusion (C := Over X)).map f) →
        IsCoveringOver J ((takeUnions (C := Over X)).map f))
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hsum : ∀ n, HasCoproduct (K.obj n).obj)
    (hK : IsHypercovering J K) :
    IsHypercovering J (takeUnionsSimplicial K hsum) :=
  isHypercovering_whiskerLift J (fun U : FormalCoproduct.{w} (Over X) ↦ HasCoproduct U.obj)
    (takeUnions.{w, v, max u v} (C := Over X)) hcover K hsum hK

end Stacks.CategoryTheory.Hypercovering

end
