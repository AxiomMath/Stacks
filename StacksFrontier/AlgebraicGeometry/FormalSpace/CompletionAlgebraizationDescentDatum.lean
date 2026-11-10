module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationAtlasBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentTransport

/-!
# The descent datum of algebraizations of a formal space over a covering

Let `Y₀` be an algebraic space, `T` a set of points of `Y₀` and `g : W ⟶ Y₀_{/T}` a morphism of
fppf sheaves. Let `{e i : X i ⟶ Y₀}` be a family of morphisms locally of finite type with locally
Noetherian sources, and suppose that over each `X i` the base change `W_i = W ×_{Y₀/T} (X i)_{/T}`
is algebraized: there is a morphism `M i ⟶ X i` locally of finite type which is an isomorphism over
the complement of the inverse image of `T`, together with an isomorphism `γ i` over `(X i)_{/T}`
between its completion and `W_i`. This is the situation of the proof of Stacks 0ARB, where `X i`
are the members of an étale covering of `Y₀` by affines and the algebraizations come from Stacks
0ARA.

This file constructs, from full faithfulness of the completion functor (Stacks 0GDR), the descent
datum `(M i, a_ij)` of the source. The gluing isomorphisms `a_ij` are pinned down by asking that
they be compatible with the morphisms to `W`; they exist by the fullness half of Stacks 0GDR over
the members `X j` of the family, and the cocycle condition holds by the faithfulness half. The
fibre products `M i ×_{Y₀} X j` are not affine, so 0GDR is used in its general form, for a locally
Noetherian source.

Rather than the isomorphisms themselves, the construction produces the *move operation*
(`CategoryTheory.FamilyTransport`) of the datum: a point of `M i` over a point of `X j` is moved to
`M j`. Its axioms are the identity and cocycle conditions, and they are checked on the universal
points, where they are equalities of morphisms to `M j` over `X j` compatible with the morphisms to
`W`.

## Main definitions

* `AlgebraicGeometry.Space.CompletionAlgebraization.toWHom`: the morphism to `W` of the completion
  of an algebraization over a chart.
* `AlgebraicGeometry.Space.CompletionAlgebraization.transport`: the move operation.
* `AlgebraicGeometry.Space.CompletionAlgebraization.descentData`: the descent datum.

## Main results

* `AlgebraicGeometry.Space.CompletionAlgebraization.eq_of_comp_toW_eq`: morphisms to an
  algebraization over `X k` which agree over `X k` and after completion and composition to `W` are
  equal (faithfulness half of Stacks 0GDR).
* `AlgebraicGeometry.Space.CompletionAlgebraization.exists_comp_toW_eq`: a morphism to `W` from the
  completion of a locally Noetherian algebraic space over `X k` comes from a morphism to the
  algebraization (fullness half of Stacks 0GDR).
* `AlgebraicGeometry.Space.CompletionAlgebraization.completionOverMap_move_comp_toWHom`: the move
  operation is compatible with the morphisms to `W`.

## Implementation notes

Stacks 0GDR enters through `AlgebraicGeometry.Space.completionOverFunctor_map_bijective`, over the
members `X j` of the family.

## References

* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

namespace CompletionAlgebraization

open AlgebraicGeometry.Space.Descent

variable {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Set (points B S hS Y₀)}
  {W : FormalSpace.FppfSheaf B S hS} (g : W ⟶ completionSheaf B S hS Y₀ T)

section Chart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ Y₀) (M : Over X)
  (γ : completionSheaf B S hS M.left
    (pointsMap B S hS M.left M.hom ⁻¹' (pointsMap B S hS X e ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS e T))
  (hγ : γ.hom ≫ pullback.snd g (completionSheafMap B S hS e T) =
    completionSheafMap B S hS M.hom (pointsMap B S hS X e ⁻¹' T))

/-- The points of the algebraization over `T`, computed over `Y₀` or over the chart. -/
theorem preimage_comp_eq :
    pointsMap B S hS M.left ((Over.map e).obj M).hom ⁻¹' T =
      pointsMap B S hS M.left M.hom ⁻¹' (pointsMap B S hS X e ⁻¹' T) :=
  preimage_pointsMap_over B S hS T (Descent.structureMap e M)

/-- The morphism to `W` of the completion along `T` of an algebraization `M` of `W` over `e`,
as a morphism of sheaves. -/
def toWHom : completionSheaf B S hS ((Over.map e).obj M).left
    (pointsMap B S hS ((Over.map e).obj M).left ((Over.map e).obj M).hom ⁻¹' T) ⟶ W :=
  eqToHom (congrArg (completionSheaf B S hS M.left) (preimage_comp_eq e M)) ≫ γ.hom ≫
    pullback.fst g (completionSheafMap B S hS e T)

/-- The completion of the structure morphism of `M` over `Y₀` to the chart. -/
theorem completionOverMap_structureMap :
    completionOverMap B S hS T (Descent.structureMap e M) =
      eqToHom (congrArg (completionSheaf B S hS M.left) (preimage_comp_eq e M)) ≫
        completionSheafMap B S hS M.hom (pointsMap B S hS X e ⁻¹' T) := rfl

include hγ in
/-- The morphism to `W` of the completion of `M`, composed with `g`, is the completion of the
structure morphism of `M` over `Y₀`. -/
theorem toWHom_comp :
    toWHom g e M γ ≫ g = completionSheafMap B S hS ((Over.map e).obj M).hom T := by
  have h := completionOverMap_comp_completionSheafMap B S hS T (Descent.structureMap e M)
  rw [completionOverMap_structureMap, Category.assoc] at h
  rw [toWHom, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc γ.hom, hγ]
  exact h

include hγ in
/-- The completion of the algebraization over `Y₀`, with its morphisms to `W` and to the
completion of the chart, is the fibre product `W ×_{Y₀/T} (X)_{/T}`. -/
theorem isPullback_toW :
    IsPullback (toWHom g e M γ) (completionOverMap B S hS T (Descent.structureMap e M)) g
      (completionSheafMap B S hS e T) := by
  rw [toWHom, completionOverMap_structureMap]
  refine (IsPullback.of_hasPullback g (completionSheafMap B S hS e T)).of_iso
    (γ.symm ≪≫ eqToIso (congrArg (completionSheaf B S hS M.left) (preimage_comp_eq e M)).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp [← hγ]

variable {g e M γ hγ}

include hγ in
/-- **Uniqueness, from the faithfulness half of Stacks 0GDR.** Two morphisms from a locally
Noetherian algebraic space over `Y₀` to the algebraization `M` over `X` which agree over `X` and
whose completions agree after composition to `W` are equal. -/
theorem eq_of_comp_toW_eq (hT : IsClosed T) (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hM : IsFiniteTypeModification B S hS
      (openSubspaceOfPoints B S hS X (pointsMap B S hS X e ⁻¹' T)ᶜ) M)
    {P : Over Y₀} (hP : IsAlgebraicSpace B S hS P.left)
    (hPnoeth : HasEtaleLocalProperty B S hS P.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {a b : P ⟶ (Over.map e).obj M}
    (hab : a ≫ Descent.structureMap e M = b ≫ Descent.structureMap e M)
    (hw : completionOverMap B S hS T a ≫ toWHom g e M γ =
      completionOverMap B S hS T b ≫ toWHom g e M γ) : a = b := by
  have h1 : completionOverMap B S hS T a = completionOverMap B S hS T b := by
    apply (isPullback_toW g e M γ hγ).hom_ext hw
    rw [← completionOverMap_comp, ← completionOverMap_comp, hab]
  have hTX : IsClosed (pointsMap B S hS X e ⁻¹' T) :=
    hT.preimage (continuous_pointsMap B S hS e)
  have hMnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hM.1.1 hX M.hom hM.2
    hXnoeth
  have hb : b.left ≫ M.hom = (a ≫ Descent.structureMap e M).left := by
    rw [hab]
    rfl
  let a' : Over.mk (a ≫ Descent.structureMap e M).left ⟶ Over.mk M.hom := Over.homMk a.left rfl
  let b' : Over.mk (a ≫ Descent.structureMap e M).left ⟶ Over.mk M.hom := Over.homMk b.left hb
  have hset : pointsMap B S hS P.left (a ≫ Descent.structureMap e M).left ⁻¹'
      (pointsMap B S hS X e ⁻¹' T) = pointsMap B S hS P.left P.hom ⁻¹' T :=
    (preimage_pointsMap_over B S hS T (a ≫ Descent.structureMap e M)).symm
  have h2 : completionSheafInclusion B S hS P.left (pointsMap B S hS P.left P.hom ⁻¹' T) ≫
      sheafifiedULiftMap B S hS a.left =
      completionSheafInclusion B S hS P.left (pointsMap B S hS P.left P.hom ⁻¹' T) ≫
      sheafifiedULiftMap B S hS b.left := by
    rw [← completionOverMap_comp_inclusion, ← completionOverMap_comp_inclusion, h1]
  have key : (completionOverFunctor B S hS (pointsMap B S hS X e ⁻¹' T)).map a' =
      (completionOverFunctor B S hS (pointsMap B S hS X e ⁻¹' T)).map b' := by
    apply Over.OverMorphism.ext
    change completionOverMap B S hS (pointsMap B S hS X e ⁻¹' T) a' =
      completionOverMap B S hS (pointsMap B S hS X e ⁻¹' T) b'
    have := mono_completionSheafInclusion B S hS (Over.mk M.hom).left
      (pointsMap B S hS (Over.mk M.hom).left (Over.mk M.hom).hom ⁻¹' (pointsMap B S hS X e ⁻¹' T))
    apply (cancel_mono (completionSheafInclusion B S hS (Over.mk M.hom).left
      (pointsMap B S hS (Over.mk M.hom).left (Over.mk M.hom).hom ⁻¹'
        (pointsMap B S hS X e ⁻¹' T)))).1
    rw [completionOverMap_comp_inclusion, completionOverMap_comp_inclusion]
    change completionSheafInclusion B S hS P.left (pointsMap B S hS P.left
        (a ≫ Descent.structureMap e M).left ⁻¹' (pointsMap B S hS X e ⁻¹' T)) ≫
        sheafifiedULiftMap B S hS a.left =
      completionSheafInclusion B S hS P.left (pointsMap B S hS P.left
        (a ≫ Descent.structureMap e M).left ⁻¹' (pointsMap B S hS X e ⁻¹' T)) ≫
        sheafifiedULiftMap B S hS b.left
    rw [← completionSheafInclusion_transport B S hS P.left hset, Category.assoc,
      Category.assoc, h2]
  have := completionOverFunctor_map_injective (g := (a ≫ Descent.structureMap e M).left)
    (f := M.hom) hP hM.1.1 hPnoeth hMnoeth hTX hM.1.2 key
  have h4 : a'.left = b'.left := congrArg CommaMorphism.left this
  exact Over.OverMorphism.ext h4

include hγ in
/-- **Existence, from the fullness half of Stacks 0GDR.** Let `P` be a locally Noetherian algebraic
space over `Y₀` with a morphism `π` to `X` over `Y₀`, and let `wP : P_{/T} ⟶ W` be a morphism over
`Y₀_{/T}`. Then there is a morphism `a : P ⟶ M` over `X` whose completion composed with the
morphism to `W` is `wP`. -/
theorem exists_comp_toW_eq (hT : IsClosed T)
    (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hM : IsFiniteTypeModification B S hS
      (openSubspaceOfPoints B S hS X (pointsMap B S hS X e ⁻¹' T)ᶜ) M)
    {P : Over Y₀} (hP : IsAlgebraicSpace B S hS P.left)
    (hPnoeth : HasEtaleLocalProperty B S hS P.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (π : P ⟶ Over.mk e)
    (wP : completionSheaf B S hS P.left (pointsMap B S hS P.left P.hom ⁻¹' T) ⟶ W)
    (hwP : wP ≫ g = completionSheafMap B S hS P.hom T) :
    ∃ a : P ⟶ (Over.map e).obj M, a ≫ Descent.structureMap e M = π ∧
      completionOverMap B S hS T a ≫ toWHom g e M γ = wP := by
  have hTX : IsClosed (pointsMap B S hS X e ⁻¹' T) :=
    hT.preimage (continuous_pointsMap B S hS e)
  have hsq := isPullback_toW g e M γ hγ
  obtain ⟨α₀, hα₀fst, hα₀snd⟩ : ∃ α₀, α₀ ≫ toWHom g e M γ = wP ∧
      α₀ ≫ completionOverMap B S hS T (Descent.structureMap e M) =
        completionOverMap B S hS T π := by
    have hc : wP ≫ g = completionOverMap B S hS T π ≫ completionSheafMap B S hS e T :=
      hwP.trans (completionOverMap_comp_completionSheafMap B S hS T π).symm
    exact ⟨hsq.lift _ _ hc, hsq.lift_fst _ _ hc, hsq.lift_snd _ _ hc⟩
  have e₁ : pointsMap B S hS P.left π.left ⁻¹' (pointsMap B S hS X e ⁻¹' T) =
      pointsMap B S hS P.left P.hom ⁻¹' T :=
    (preimage_pointsMap_over B S hS T π).symm
  have e₂ := preimage_pointsMap_over B S hS T (Descent.structureMap e M)
  have hw' : eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫ α₀ ≫
      completionOverMap B S hS T (Descent.structureMap e M) =
        completionSheafMap B S hS π.left (pointsMap B S hS X e ⁻¹' T) := by
    rw [hα₀snd, completionOverMap, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl
  have hw'' : (eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫ α₀ ≫
      eqToHom (congrArg (completionSheaf B S hS ((Over.map e).obj M).left) e₂)) ≫
        completionSheafMap B S hS M.hom (pointsMap B S hS X e ⁻¹' T) =
      completionSheafMap B S hS π.left (pointsMap B S hS X e ⁻¹' T) :=
    ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).trans hw'
  obtain ⟨a', ha'⟩ := (completionOverFunctor_map_bijective hX hXnoeth hTX hM.1.1 hM.2 hM.1.2
    π.left hP hPnoeth).2
    (Over.homMk (eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫ α₀ ≫
      eqToHom (congrArg (completionSheaf B S hS ((Over.map e).obj M).left) e₂)) hw'')
  have ha'w : a'.left ≫ M.hom = π.left := Over.w a'
  let a : P ⟶ (Over.map e).obj M := Over.homMk a'.left (by
    change a'.left ≫ M.hom ≫ e = P.hom
    rw [← Category.assoc, ha'w, show π.left ≫ e = P.hom from Over.w π])
  refine ⟨a, Over.OverMorphism.ext ha'w, ?_⟩
  rw [← hα₀fst]
  suffices h : completionOverMap B S hS T a = α₀ by rw [h]
  have := mono_completionSheafInclusion B S hS ((Over.map e).obj M).left
    (pointsMap B S hS ((Over.map e).obj M).left ((Over.map e).obj M).hom ⁻¹' T)
  apply (cancel_mono (completionSheafInclusion B S hS ((Over.map e).obj M).left
    (pointsMap B S hS ((Over.map e).obj M).left ((Over.map e).obj M).hom ⁻¹' T))).1
  have h6 := congrArg (fun φ => φ.left ≫ completionSheafInclusion B S hS (Over.mk M.hom).left
    (pointsMap B S hS (Over.mk M.hom).left (Over.mk M.hom).hom ⁻¹' (pointsMap B S hS X e ⁻¹' T)))
    ha'
  have h7 := (completionOverMap_comp_inclusion B S hS (pointsMap B S hS X e ⁻¹' T) a').symm.trans
    h6
  rw [completionOverMap_comp_inclusion]
  have h10 : eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫
      (completionSheafInclusion B S hS P.left (pointsMap B S hS P.left P.hom ⁻¹' T) ≫
        sheafifiedULiftMap B S hS a.left) =
      eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫
        (α₀ ≫ completionSheafInclusion B S hS ((Over.map e).obj M).left
          (pointsMap B S hS ((Over.map e).obj M).left ((Over.map e).obj M).hom ⁻¹' T)) := by
    rw [← Category.assoc, completionSheafInclusion_transport B S hS P.left e₁]
    refine h7.trans ?_
    change (eqToHom (congrArg (completionSheaf B S hS P.left) e₁) ≫ α₀ ≫
      eqToHom (congrArg (completionSheaf B S hS ((Over.map e).obj M).left) e₂)) ≫
        completionSheafInclusion B S hS ((Over.map e).obj M).left
          (pointsMap B S hS ((Over.map e).obj M).left (Descent.structureMap e M).left ⁻¹'
            (pointsMap B S hS (Over.mk e).left (Over.mk e).hom ⁻¹' T)) = _
    rw [Category.assoc, Category.assoc,
      completionSheafInclusion_transport B S hS ((Over.map e).obj M).left e₂]
  exact (cancel_epi _).1 h10

end Chart

/-! ### Products over `Y₀` with a member of the family -/

section Products

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ Y₀)

/-- The product over `Y₀` of an algebraic space with `X` is an algebraic space. -/
theorem isAlgebraicSpace_prod_left (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX : IsAlgebraicSpace B S hS X) {Q : Over Y₀} (hQ : IsAlgebraicSpace B S hS Q.left) :
    IsAlgebraicSpace B S hS (Q ⨯ Over.mk e).left :=
  (isAlgebraicSpace_pullback B S hS Q.hom e hQ hX hY₀).of_iso
    (Over.prodLeftIsoPullback Q (Over.mk e)).symm

/-- The second projection of the product over `Y₀` of a space locally of finite type over `Y₀`
with `X` is locally of finite type. -/
theorem isLocallyOfFiniteType_prod_snd_left (hY₀ : IsAlgebraicSpace B S hS Y₀)
    {Q : Over Y₀} (hQ : IsAlgebraicSpace B S hS Q.left)
    (hQft : IsLocallyOfFiniteType B S hS Q.hom) :
    IsLocallyOfFiniteType B S hS (prod.snd : Q ⨯ Over.mk e ⟶ Over.mk e).left :=
  IsLocallyOfFiniteType.of_isPullback B S hS
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Q (Over.mk e))).flip hQ hY₀ hQft

/-- The product over `Y₀` of a space locally of finite type over `Y₀` with `X` is locally of
finite type over `Y₀` when `X` is. -/
theorem isLocallyOfFiniteType_prod_hom (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX : IsAlgebraicSpace B S hS X) (he : IsLocallyOfFiniteType B S hS e)
    {Q : Over Y₀} (hQ : IsAlgebraicSpace B S hS Q.left)
    (hQft : IsLocallyOfFiniteType B S hS Q.hom) :
    IsLocallyOfFiniteType B S hS (Q ⨯ Over.mk e).hom := by
  rw [← Over.w (prod.snd : Q ⨯ Over.mk e ⟶ Over.mk e)]
  exact isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_prod_left e hY₀ hX hQ) hX hY₀ _ e
    (isLocallyOfFiniteType_prod_snd_left e hY₀ hQ hQft) he

/-- The product over `Y₀` of a space locally of finite type over `Y₀` with a locally Noetherian
`X` is locally Noetherian. -/
theorem isLocallyNoetherian_prod_left (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {Q : Over Y₀} (hQ : IsAlgebraicSpace B S hS Q.left)
    (hQft : IsLocallyOfFiniteType B S hS Q.hom) :
    HasEtaleLocalProperty B S hS (Q ⨯ Over.mk e).left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (isAlgebraicSpace_prod_left e hY₀ hX hQ) hX
    _ (isLocallyOfFiniteType_prod_snd_left e hY₀ hQ hQft) hXnoeth

end Products

/-! ### The move operation and the descent datum -/

section Family

variable (hT : IsClosed T)
  (hY₀ : IsAlgebraicSpace B S hS Y₀)
  {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀}
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
  (hXnoeth : ∀ i, HasEtaleLocalProperty B S hS (X i)
    (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
  (he : ∀ i, IsLocallyOfFiniteType B S hS (e i))
  {M : ∀ i, Over (X i)}
  (hM : ∀ i, IsFiniteTypeModification B S hS
    (openSubspaceOfPoints B S hS (X i) (pointsMap B S hS (X i) (e i) ⁻¹' T)ᶜ) (M i))
  (γ : ∀ i, completionSheaf B S hS (M i).left
    (pointsMap B S hS (M i).left (M i).hom ⁻¹' (pointsMap B S hS (X i) (e i) ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS (e i) T))
  (hγ : ∀ i, (γ i).hom ≫ pullback.snd g (completionSheafMap B S hS (e i) T) =
    completionSheafMap B S hS (M i).hom (pointsMap B S hS (X i) (e i) ⁻¹' T))

include hY₀ hX he hM in
/-- The algebraization `M i`, as a space over `Y₀`, is locally of finite type over `Y₀`. -/
theorem isLocallyOfFiniteType_map_obj_hom (i : ι) :
    IsLocallyOfFiniteType B S hS ((Over.map (e i)).obj (M i)).hom :=
  isLocallyOfFiniteType_comp B S hS (hM i).1.1 (hX i) hY₀ (M i).hom (e i) (hM i).2 (he i)

include hY₀ hX hXnoeth he hM in
/-- The universal point of `M i` over a point of `X j` lives on a locally Noetherian algebraic
space. -/
theorem prod_left_props (i j : ι) :
    IsAlgebraicSpace B S hS ((Over.map (e i)).obj (M i) ⨯ Over.mk (e j)).left ∧
      HasEtaleLocalProperty B S hS ((Over.map (e i)).obj (M i) ⨯ Over.mk (e j)).left
        (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
  ⟨isAlgebraicSpace_prod_left (e j) hY₀ (hX j) (hM i).1.1,
    isLocallyNoetherian_prod_left (e j) hY₀ (hX j) (hXnoeth j) (hM i).1.1
      (isLocallyOfFiniteType_map_obj_hom hY₀ hX he hM i)⟩

include hγ in
/-- The morphism to `W` of the completion of the universal point of `M i` over `X j`. -/
theorem universal_toWHom_comp (i j : ι) :
    (completionOverMap B S hS T (prod.fst : (Over.map (e i)).obj (M i) ⨯ Over.mk (e j) ⟶ _) ≫
      toWHom g (e i) (M i) (γ i)) ≫ g =
      completionSheafMap B S hS ((Over.map (e i)).obj (M i) ⨯ Over.mk (e j)).hom T := by
  rw [Category.assoc, toWHom_comp g (e i) (M i) (γ i) (hγ i),
    completionOverMap_comp_completionSheafMap]

/-- The universal move: the morphism from `M i ×_{Y₀} X j` to `M j` over `X j` compatible with
the morphisms to `W`, provided by the fullness half of Stacks 0GDR over `X j`. -/
def move (i j : ι) : (Over.map (e i)).obj (M i) ⨯ Over.mk (e j) ⟶ (Over.map (e j)).obj (M j) :=
  (exists_comp_toW_eq (γ := γ j) (hγ := hγ j) hT (hX j) (hXnoeth j) (hM j)
    (prod_left_props hY₀ hX hXnoeth he hM i j).1 (prod_left_props hY₀ hX hXnoeth he hM i j).2
    prod.snd _ (universal_toWHom_comp g γ hγ i j)).choose

/-- The defining properties of the universal move. -/
private theorem move_spec (i j : ι) :
    move g hT hY₀ hX hXnoeth he hM γ hγ i j ≫ Descent.structureMap (e j) (M j) = prod.snd ∧
      completionOverMap B S hS T (move g hT hY₀ hX hXnoeth he hM γ hγ i j) ≫
        toWHom g (e j) (M j) (γ j) =
      completionOverMap B S hS T prod.fst ≫ toWHom g (e i) (M i) (γ i) :=
  (exists_comp_toW_eq (γ := γ j) (hγ := hγ j) hT (hX j) (hXnoeth j) (hM j)
    (prod_left_props hY₀ hX hXnoeth he hM i j).1 (prod_left_props hY₀ hX hXnoeth he hM i j).2
    prod.snd _ (universal_toWHom_comp g γ hγ i j)).choose_spec

/-- The universal move lies over `X j`: composed with the structure morphism of `M j`, it is the
second projection. -/
theorem move_comp_structureMap (i j : ι) :
    move g hT hY₀ hX hXnoeth he hM γ hγ i j ≫ Descent.structureMap (e j) (M j) =
      prod.snd :=
  (move_spec g hT hY₀ hX hXnoeth he hM γ hγ i j).1

/-- The universal move is compatible with the morphisms to `W`: the completion of the universal
move followed by the morphism to `W` of `M j` equals the completion of the first projection
followed by the morphism to `W` of `M i`. -/
theorem map_move_comp_toW_universal (i j : ι) :
    completionOverMap B S hS T (move g hT hY₀ hX hXnoeth he hM γ hγ i j) ≫
        toWHom g (e j) (M j) (γ j) =
      completionOverMap B S hS T prod.fst ≫ toWHom g (e i) (M i) (γ i) :=
  (move_spec g hT hY₀ hX hXnoeth he hM γ hγ i j).2

include hT hY₀ hX hXnoeth he hM in
/-- Moving a point to its own image does nothing, on the universal point. -/
theorem lift_id_move_self (i : ι) :
    prod.lift (𝟙 _) (Descent.structureMap (e i) (M i)) ≫
      move g hT hY₀ hX hXnoeth he hM γ hγ i i = 𝟙 _ := by
  refine eq_of_comp_toW_eq (γ := γ i) (hγ := hγ i) hT (hX i) (hXnoeth i) (hM i)
    (P := (Over.map (e i)).obj (M i)) (hM i).1.1
    (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (hM i).1.1 (hX i) _ (hM i).2
      (hXnoeth i)) ?_ ?_
  · rw [Category.assoc, move_comp_structureMap, prod.lift_snd, Category.id_comp]
  · rw [completionOverMap_comp, Category.assoc, map_move_comp_toW_universal, ← Category.assoc,
      ← completionOverMap_comp, prod.lift_fst]

include hT hY₀ hX hXnoeth he hM in
/-- Moving twice is moving once, on the universal point. -/
theorem lift_move_move (i j k : ι) :
    prod.lift (prod.fst ≫ move g hT hY₀ hX hXnoeth he hM γ hγ i j) prod.snd ≫
        move g hT hY₀ hX hXnoeth he hM γ hγ j k =
      prod.lift (prod.fst ≫ prod.fst) prod.snd ≫
        move g hT hY₀ hX hXnoeth he hM γ hγ i k := by
  have hQ := prod_left_props hY₀ hX hXnoeth he hM i j
  have hQft : IsLocallyOfFiniteType B S hS ((Over.map (e i)).obj (M i) ⨯ Over.mk (e j)).hom :=
    isLocallyOfFiniteType_prod_hom (e j) hY₀ (hX j) (he j) (hM i).1.1
      (isLocallyOfFiniteType_map_obj_hom hY₀ hX he hM i)
  refine eq_of_comp_toW_eq (γ := γ k) (hγ := hγ k) hT (hX k) (hXnoeth k) (hM k)
    (isAlgebraicSpace_prod_left (e k) hY₀ (hX k) hQ.1)
    (isLocallyNoetherian_prod_left (e k) hY₀ (hX k) (hXnoeth k) hQ.1 hQft) ?_ ?_
  · rw [Category.assoc, Category.assoc, move_comp_structureMap, move_comp_structureMap,
      prod.lift_snd, prod.lift_snd]
  · simp only [completionOverMap_comp, Category.assoc, map_move_comp_toW_universal]
    simp only [← Category.assoc, ← completionOverMap_comp, prod.lift_fst]
    simp only [completionOverMap_comp, Category.assoc, map_move_comp_toW_universal]

/-- **The move operation of the descent datum of algebraizations.** A point `v` of `M i` over a
point `y` of `X j` is moved to `M j` by the universal move
`AlgebraicGeometry.Space.CompletionAlgebraization.move`. -/
def transport :
    FamilyTransport (fun i ↦ (Over.map (e i)).obj (M i)) (fun i ↦ Over.mk (e i))
      (fun i ↦ Descent.structureMap (e i) (M i)) where
  move := fun {i j _} v y => prod.lift v y ≫ move g hT hY₀ hX hXnoeth he hM γ hγ i j
  comp_move k v y := by rw [← Category.assoc, prod.comp_lift]
  move_base v y := by rw [Category.assoc, move_comp_structureMap, prod.lift_snd]
  move_self := fun {i _} v => by
    have h : prod.lift v (v ≫ Descent.structureMap (e i) (M i)) =
        v ≫ prod.lift (𝟙 _) (Descent.structureMap (e i) (M i)) := by
      rw [prod.comp_lift, Category.comp_id]
    rw [h, Category.assoc, lift_id_move_self, Category.comp_id]
  move_comp := fun {i j k _} v y z => by
    have h₁ : prod.lift (prod.lift v y ≫ move g hT hY₀ hX hXnoeth he hM γ hγ i j) z =
        prod.lift (prod.lift v y) z ≫
          prod.lift (prod.fst ≫ move g hT hY₀ hX hXnoeth he hM γ hγ i j) prod.snd := by
      rw [prod.comp_lift, prod.lift_fst_assoc, prod.lift_snd]
    have h₂ : prod.lift v z = prod.lift (prod.lift v y) z ≫ prod.lift (prod.fst ≫ prod.fst)
        prod.snd := by
      rw [prod.comp_lift, prod.lift_fst_assoc, prod.lift_fst, prod.lift_snd]
    rw [h₁, h₂, Category.assoc, Category.assoc, lift_move_move]

/-- Moving a point `v` of `M i` over a point `y` of `X j` is the composition of `(v, y)` with the
universal move. -/
@[simp]
theorem transport_move {i j : ι} {Z : Over Y₀} (v : Z ⟶ (Over.map (e i)).obj (M i))
    (y : Z ⟶ Over.mk (e j)) :
    (transport g hT hY₀ hX hXnoeth he hM γ hγ).move v y =
      prod.lift v y ≫ move g hT hY₀ hX hXnoeth he hM γ hγ i j := rfl

/-- **The move operation is compatible with the morphisms to `W`.** -/
theorem completionOverMap_move_comp_toWHom {i j : ι} {Z : Over Y₀}
    (v : Z ⟶ (Over.map (e i)).obj (M i)) (y : Z ⟶ Over.mk (e j)) :
    completionOverMap B S hS T ((transport g hT hY₀ hX hXnoeth he hM γ hγ).move v y) ≫
        toWHom g (e j) (M j) (γ j) =
      completionOverMap B S hS T v ≫ toWHom g (e i) (M i) (γ i) := by
  rw [transport_move, completionOverMap_comp, Category.assoc, map_move_comp_toW_universal,
    ← Category.assoc, ← completionOverMap_comp, prod.lift_fst]

/-- **The descent datum of the algebraizations** `(M i, a_ij)`, relative to an fppf covering
`{e i : X i ⟶ Y₀}`. Its gluing isomorphisms are those of the move operation
`AlgebraicGeometry.Space.CompletionAlgebraization.transport`, so they satisfy the cocycle
condition. -/
def descentData (hcov : IsFppfCovering B S hS X e) :
    Space.Descent.DescentData e hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace where
  obj := M
  obj_isAlgebraicSpace i := (hM i).1.1
  gluing i j := (transport g hT hY₀ hX hXnoeth he hM γ hγ).gluing i j
  cocycle i j k := (transport g hT hY₀ hX hXnoeth he hM γ hγ).gluing_cocycle i j k

/-- The object of the descent datum over `X i` is the algebraization `M i`. -/
@[simp]
theorem descentData_obj (hcov : IsFppfCovering B S hS X e) (i : ι) :
    (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov).obj i = M i := rfl

/-- The move operation of the descent datum is the move operation it was built from. -/
theorem descentData_transport_move (hcov : IsFppfCovering B S hS X e) {i j : ι} {Z : Over Y₀}
    (v : Z ⟶ (Over.map (e i)).obj (M i)) (y : Z ⟶ Over.mk (e j)) :
    (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov).transport.move v y =
      (transport g hT hY₀ hX hXnoeth he hM γ hγ).move v y := by
  change prod.lift v y ≫ ((transport g hT hY₀ hX hXnoeth he hM γ hγ).gluing i j).hom.left ≫
    prod.snd = _
  rw [FamilyTransport.gluing_hom, prod.lift_snd,
    (transport g hT hY₀ hX hXnoeth he hM γ hγ).comp_move, prod.lift_fst, prod.lift_snd]

end Family

end CompletionAlgebraization

end AlgebraicGeometry.Space

end
