module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.KrullTopology
public import StacksCore.Tactic.StacksAttribute

/-!
# Galois actions on quasi-compact opens

A quasi-compact open in the base change of a scheme to a Galois extension descends to a
finite intermediate extension. Consequently, an open subgroup of the Galois group stabilizes
the open.

## Main definitions

* `AlgebraicGeometry.spectrumMap` is the morphism of spectra associated to an algebra structure.

## Main results

* `AlgebraicGeometry.exists_finite_subextension_descending_isCompact_open` gives descent to a
  finite intermediate extension.
* `AlgebraicGeometry.exists_open_subgroup_fixing_isCompact_open` gives an open stabilizer in the
  Galois group.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

/-- The morphism `Spec L ⟶ Spec k` associated to a `k`-algebra `L`. -/
public abbrev spectrumMap (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- The automorphism of the base change induced by a Galois automorphism of the extension. -/
private noncomputable def galoisActionIso
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    pullback f (spectrumMap k K) ≅ pullback f (spectrumMap k K) := by
  let e := σ.toRingEquiv.toCommRingCatIso
  let : IsIso (Spec.map e.hom) := by
    change IsIso (Scheme.Spec.map e.hom.op)
    exact Functor.map_isIso Scheme.Spec e.hom.op
  let m := pullback.map f (spectrumMap k K) f (spectrumMap k K)
    (𝟙 X) (Spec.map e.hom) (𝟙 _) (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (algebraMap k K)) = _
      rw [Spec.map_inj]
      ext x
      exact (σ.commutes x).symm)
  have hm : IsIso m := by
    dsimp [m]
    infer_instance
  exact asIso m

/-- The Galois automorphism of the base change commutes with the projection to `X`. -/
@[reassoc (attr := simp)]
private lemma galoisActionIso_fst
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (galoisActionIso f σ).hom ≫ pullback.fst f (spectrumMap k K) =
      pullback.fst f (spectrumMap k K) := by
  simp [galoisActionIso, pullback.map, pullback.lift_fst]

/-- The Galois automorphism of the base change acts on the second projection through the
automorphism of the extension. -/
@[reassoc (attr := simp)]
private lemma galoisActionIso_snd
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (galoisActionIso f σ).hom ≫ pullback.snd f (spectrumMap k K) =
      pullback.snd f (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) := by
  simp [galoisActionIso, pullback.map, pullback.lift_snd]

/-- A Galois automorphism fixing an intermediate field acts trivially on the base change
descended to that field. -/
private lemma galoisActionIso_comp_desc
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (E : IntermediateField k K) [FiniteDimensional k E] (σ : Gal(K/k))
    (hσ : σ ∈ E.fixingSubgroup)
    (p : pullback f (spectrumMap k K) ⟶ pullback f (spectrumMap k E))
    (hp₁ : p ≫ pullback.fst f (spectrumMap k E) = pullback.fst f (spectrumMap k K))
    (hp₂ : p ≫ pullback.snd f (spectrumMap k E) =
      pullback.snd f (spectrumMap k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) :
    (galoisActionIso f σ).hom ≫ p = p := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hincl : Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E K)) =
        Spec.map (CommRingCat.ofHom (algebraMap E K)) := by
    rw [← Spec.map_comp, Spec.map_inj]
    ext x
    exact hσ x.1 x.2
  apply pullback.hom_ext
  · simp only [Category.assoc, hp₁, galoisActionIso_fst]
  · simp only [Category.assoc, hp₂, galoisActionIso_snd_assoc, hincl]

/-- The finite subextensions of a field extension, ordered by inclusion. -/
public abbrev FExt (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  {E : IntermediateField k K // FiniteDimensional k E}

/-- The finite subextensions of a field extension form a filtered category. -/
public instance (k K : Type u) [Field k] [Field K] [Algebra k K] :
    IsFiltered (FExt k K) where
  cocone_objs A B := by
    have := A.2
    have := B.2
    exact ⟨⟨A.1 ⊔ B.1, IntermediateField.finiteDimensional_sup A.1 B.1⟩,
      homOfLE (show A.1 ≤ A.1 ⊔ B.1 from le_sup_left),
      homOfLE (show B.1 ≤ A.1 ⊔ B.1 from le_sup_right), trivial⟩
  cocone_maps _ B _ _ := ⟨B, 𝟙 B, by subsingleton⟩
  nonempty := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram of finite subextensions, as commutative rings. -/
public def fextDiagram (k K : Type u) [Field k] [Field K] [Algebra k K] :
    FExt k K ⥤ CommRingCat where
  obj E := CommRingCat.of E.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The cocone on the diagram of finite subextensions with vertex the whole extension. -/
public def fextCocone (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Cocone (fextDiagram k K) where
  pt := CommRingCat.of K
  ι := {
    app E := CommRingCat.ofHom E.1.val.toRingHom
    naturality _ _ f := by ext x; rfl
  }

/-- The finite subextension generated by one algebraic element. -/
public noncomputable def fextStage {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (x : K) : FExt k K :=
  ⟨IntermediateField.adjoin k {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

/-- Evaluation of a cocone leg at the stage generated by an element. -/
public noncomputable def fextEvalAtStage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (s : Cocone (fextDiagram k K)) (x : K) : s.pt :=
  (s.ι.app (fextStage x)).hom ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩

/-- Evaluation at a stage is computed by any subextension containing the element. -/
public lemma fextEvalAtStage_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (s : Cocone (fextDiagram k K)) (E : FExt k K) (x : K) (hx : x ∈ E.1) :
    fextEvalAtStage s x = (s.ι.app E).hom ⟨x, hx⟩ := by
  have hle : (fextStage x).1 ≤ E.1 :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact (congrArg (fun q : CommRingCat.of (fextStage x).1 ⟶ s.pt ↦
    q.hom ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩) (s.ι.naturality (homOfLE hle))).symm

/-- The ring homomorphism out of the whole extension induced by a cocone. -/
public noncomputable def fextDescHom
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (s : Cocone (fextDiagram k K)) : K →+* s.pt := by
  refine {
    toFun := fextEvalAtStage s
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_
  }
  · rw [fextEvalAtStage_eq s (fextStage 1) 1 (IntermediateField.mem_adjoin_simple_self k 1)]
    exact (s.ι.app (fextStage 1)).hom.map_one
  · intro x y
    let : FiniteDimensional k (fextStage x).1 := (fextStage x).2
    let : FiniteDimensional k (fextStage y).1 := (fextStage y).2
    let E : FExt k K := ⟨(fextStage x).1 ⊔ (fextStage y).1,
      IntermediateField.finiteDimensional_sup (fextStage x).1 (fextStage y).1⟩
    have hx : x ∈ E.1 := (show (fextStage x).1 ≤ E.1 from le_sup_left)
      (IntermediateField.mem_adjoin_simple_self k x)
    have hy : y ∈ E.1 := (show (fextStage y).1 ≤ E.1 from le_sup_right)
      (IntermediateField.mem_adjoin_simple_self k y)
    rw [fextEvalAtStage_eq s E (x * y) (E.1.mul_mem hx hy), fextEvalAtStage_eq s E x hx,
      fextEvalAtStage_eq s E y hy]
    exact map_mul (s.ι.app E).hom ⟨x, hx⟩ ⟨y, hy⟩
  · rw [fextEvalAtStage_eq s (fextStage 0) 0 (IntermediateField.mem_adjoin_simple_self k 0)]
    exact (s.ι.app (fextStage 0)).hom.map_zero
  · intro x y
    let : FiniteDimensional k (fextStage x).1 := (fextStage x).2
    let : FiniteDimensional k (fextStage y).1 := (fextStage y).2
    let E : FExt k K := ⟨(fextStage x).1 ⊔ (fextStage y).1,
      IntermediateField.finiteDimensional_sup (fextStage x).1 (fextStage y).1⟩
    have hx : x ∈ E.1 := (show (fextStage x).1 ≤ E.1 from le_sup_left)
      (IntermediateField.mem_adjoin_simple_self k x)
    have hy : y ∈ E.1 := (show (fextStage y).1 ≤ E.1 from le_sup_right)
      (IntermediateField.mem_adjoin_simple_self k y)
    rw [fextEvalAtStage_eq s E (x + y) (E.1.add_mem hx hy), fextEvalAtStage_eq s E x hx,
      fextEvalAtStage_eq s E y hy]
    exact map_add (s.ι.app E).hom ⟨x, hx⟩ ⟨y, hy⟩

/-- An algebraic extension is the filtered colimit of its finite subextensions. -/
public noncomputable def fextCoconeIsColimit
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    IsColimit (fextCocone k K) := by
  classical
  let : Field ↑(fextCocone k K).pt := by
    dsimp [fextCocone]
    infer_instance
  let : Algebra k ↑(fextCocone k K).pt := by
    dsimp [fextCocone]
    infer_instance
  let : Algebra.IsAlgebraic k ↑(fextCocone k K).pt := by
    dsimp [fextCocone]
    infer_instance
  refine {
    desc := fun s ↦ CommRingCat.ofHom (fextDescHom s)
    fac := ?_
    uniq := ?_ }
  · intro s E
    ext x
    exact fextEvalAtStage_eq s E x.1 x.2
  · intro s m hm
    ext x
    have he := congrArg (fun q : CommRingCat.of (fextStage x).1 ⟶ s.pt ↦
      q.hom ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩) (hm (fextStage x))
    have he' : m.hom x = fextEvalAtStage s x := by
      change m.hom ((fextStage x).1.val
        ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩) =
        (s.ι.app (fextStage x)).hom ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ at he
      have hcoe : ((fextStage x).1.val
          ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : K) = x := rfl
      rw [hcoe] at he
      simpa [fextEvalAtStage] using he
    change m.hom x = fextEvalAtStage s x
    exact he'

/-- The diagram of spectra of the finite subextensions. -/
public abbrev fextSpecDiagram {k K : Type u} [Field k] [Field K] [Algebra k K] :=
  (fextDiagram k K).op ⋙ Scheme.Spec

/-- The cone of spectra over the finite subextensions. -/
public noncomputable def fextSpecCone
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Cone (fextSpecDiagram (k := k) (K := K)) :=
  Scheme.Spec.mapCone (fextCocone k K).op

/-- The spectrum of an algebraic extension is the limit of the spectra of its finite
subextensions. -/
public noncomputable def fextSpecConeIsLimit
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    IsLimit (fextSpecCone (k := k) (K := K)) :=
  isLimitOfPreserves Scheme.Spec (fextCoconeIsColimit (k := k) (K := K)).op

/-- The diagram of finite subextensions, as schemes over `Spec k`. -/
public def fextOverDiagram
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    (FExt k K)ᵒᵖ ⥤ Over (Scheme.Spec.obj (op (CommRingCat.of k))) where
  obj i := Over.mk (spectrumMap k i.unop.1)
  map {i j} f := by
    refine Over.homMk (Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)) (by
      dsimp [Over.mk, spectrumMap]
      rw [← Spec.map_comp, Spec.map_inj]
      ext x
      rfl)
  map_id i := by
    ext
    dsimp [fextSpecDiagram, fextDiagram]
    simp
  map_comp f g := by
    ext
    simp only [Over.homMk_left, Over.comp_left]
    rw [← Spec.map_comp, Spec.map_inj]
    ext x
    rfl

/-- The cone over the diagram of finite subextensions in schemes over `Spec k`. -/
public noncomputable def fextOverCone
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Cone (fextOverDiagram (k := k) (K := K)) where
  pt := Over.mk (spectrumMap k K)
  π.app i := by
    change Over.mk (spectrumMap k K) ⟶ Over.mk (spectrumMap k i.unop.1)
    refine Over.homMk (Scheme.Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)).op) (by
      change Scheme.Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)).op ≫
        Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))
      rw [Scheme.Spec_map]
      rw [← Spec.map_comp, Spec.map_inj]
      exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k i.unop.1 K).symm)
  π.naturality i j f := by
    ext
    change Spec.map (CommRingCat.ofHom (algebraMap j.unop.1 K)) =
      Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)) ≫
        Spec.map (CommRingCat.ofHom
          (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
    rw [← Spec.map_comp, Spec.map_inj]
    ext x
    rfl

/-- The cone of spectra over the finite subextensions is a limit cone over `Spec k`. -/
public noncomputable def fextOverConeIsLimit
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    IsLimit (fextOverCone (k := k) (K := K)) := by
  have : IsCofiltered ((FExt k K)ᵒᵖ) := inferInstance
  have : IsConnected ((FExt k K)ᵒᵖ) := IsCofiltered.isConnected _
  let e : fextOverDiagram (k := k) (K := K) ⋙ Over.forget _ ≅
      fextSpecDiagram (k := k) (K := K) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro i j f
      rfl)
  let c₁ := (Over.forget (Scheme.Spec.obj (op (CommRingCat.of k)))).mapCone
    (fextOverCone (k := k) (K := K))
  have hc₂ : IsLimit ((Cone.postcompose e.hom).obj c₁) := by
    apply IsLimit.ofIsoLimit (fextSpecConeIsLimit (k := k) (K := K))
    apply Cone.ext (Iso.refl _)
  apply isLimitOfReflects (Over.forget _)
  exact hc₂

/-- The diagram of base changes of `f` to the finite subextensions. -/
public def fextPullbackDiagram
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    (FExt k K)ᵒᵖ ⥤ Scheme :=
  fextOverDiagram (k := k) (K := K) ⋙ Over.pullback f ⋙ Over.forget X

/-- The cone of base changes of `f` to the finite subextensions. -/
public noncomputable def fextPullbackCone
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    Cone (fextPullbackDiagram (k := k) (K := K) X f) where
  pt := pullback (spectrumMap k K) f
  π.app i := ((Over.pullback f).map
    ((fextOverCone (k := k) (K := K)).π.app i)).left
  π.naturality i j g := by
    change ((Over.pullback f).map
        ((fextOverCone (k := k) (K := K)).π.app j)).left =
      ((Over.pullback f).map ((fextOverCone (k := k) (K := K)).π.app i)).left ≫
        ((Over.pullback f).map ((fextOverDiagram (k := k) (K := K)).map g)).left
    rw [← Over.comp_left, ← Functor.map_comp, (fextOverCone (k := k) (K := K)).w g]

/-- The base change to an algebraic extension is the limit of the base changes to the finite
subextensions. -/
public noncomputable def fextPullbackConeIsLimit
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    IsLimit (fextPullbackCone (k := k) (K := K) X f) := by
  have : IsCofiltered ((FExt k K)ᵒᵖ) := inferInstance
  have : IsConnected ((FExt k K)ᵒᵖ) := IsCofiltered.isConnected _
  let cOld := (Over.forget X).mapCone
    ((Over.pullback f).mapCone (fextOverCone (k := k) (K := K)))
  have hcOld : IsLimit cOld := isLimitOfPreserves (Over.forget X)
    (isLimitOfPreserves (Over.pullback f) (fextOverConeIsLimit (k := k) (K := K)))
  apply IsLimit.ofIsoLimit hcOld
  refine Cone.ext (Iso.refl cOld.pt) ?_
  intro i
  rfl

/-- The transition morphisms in the diagram of base changes are affine. -/
public lemma fextPullbackTransition_isAffineHom
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((fextPullbackDiagram (k := k) (K := K) X f).map g) := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
    ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hg⟩
  show IsAffineHom
    (((Over.pullback f).map ((fextOverDiagram (k := k) (K := K)).map g)).left)
  have hp : ∀ l, IsAffineHom
      (pullback.snd ((fextOverDiagram (k := k) (K := K)).obj l).hom f) := fun l ↦ by
    dsimp [fextOverDiagram]
    apply MorphismProperty.pullback_snd
    infer_instance
  have heq : ((Over.pullback f).map
      ((fextOverDiagram (k := k) (K := K)).map g)).left ≫
        pullback.snd ((fextOverDiagram (k := k) (K := K)).obj j).hom f =
      pullback.snd ((fextOverDiagram (k := k) (K := K)).obj i).hom f := by
    simpa [Over.pullback_map_left] using
      (pullback.lift_snd
        (pullback.fst ((fextOverDiagram (k := k) (K := K)).obj i).hom f ≫
          Over.Hom.left ((fextOverDiagram (k := k) (K := K)).map g))
        (pullback.snd ((fextOverDiagram (k := k) (K := K)).obj i).hom f)
        (by simp [pullback.condition]))
  have := hp j
  have : IsAffineHom (((Over.pullback f).map ((fextOverDiagram (k := k) (K := K)).map g)).left ≫
      pullback.snd ((fextOverDiagram (k := k) (K := K)).obj j).hom f) := heq ▸ hp i
  exact IsAffineHom.of_comp _ (pullback.snd ((fextOverDiagram (k := k) (K := K)).obj j).hom f)

/-- An isomorphism of schemes pulls quasi-compact opens back to quasi-compact opens. -/
private lemma compact_preimage_of_schemeIso
    {A B : Scheme.{u}} (e : A ≅ B) (W : B.Opens)
    (hW : IsCompact W.1) : IsCompact (e.hom ⁻¹ᵁ W).1 :=
  e.hom.homeomorph.isCompact_preimage.mpr hW

/-- The morphism of spectra induced by the algebra map of an intermediate field into the
extension is the one induced by its inclusion. -/
private lemma specMap_intermediateField_val {k K : Type u} [Field k] [Field K]
    [Algebra k K] (E : IntermediateField k K) :
    Spec.map (CommRingCat.ofHom (algebraMap E K)) =
      Spec.map (CommRingCat.ofHom E.val) := rfl

/-- A quasi-compact open in the base change of a scheme to an algebraic extension is pulled back
from a quasi-compact open after a finite intermediate extension. -/
@[stacks 04KU "part (1)"]
public theorem exists_finite_subextension_descending_isCompact_open
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (V : (pullback f (spectrumMap k K)).Opens) (hV : IsCompact V.1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (V' : (pullback f (spectrumMap k E)).Opens),
      IsCompact V'.1 ∧
        ∃ p : pullback f (spectrumMap k K) ⟶ pullback f (spectrumMap k E),
          p ≫ pullback.fst f (spectrumMap k E) = pullback.fst f (spectrumMap k K) ∧
          p ≫ pullback.snd f (spectrumMap k E) =
            pullback.snd f (spectrumMap k K) ≫ Spec.map (CommRingCat.ofHom E.val) ∧
          V = p ⁻¹ᵁ V' := by
  let eK : pullback f (spectrumMap k K) ≅
      (fextPullbackCone (k := k) (K := K) X f).pt :=
    pullbackSymmetry f (spectrumMap k K)
  let UK : (fextPullbackCone (k := k) (K := K) X f).pt.Opens := eK.inv ⁻¹ᵁ V
  have hUK : IsCompact (UK : Set (fextPullbackCone (k := k) (K := K) X f).pt) :=
    compact_preimage_of_schemeIso eK.symm V hV
  have : ∀ {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j),
      IsAffineHom ((fextPullbackDiagram (k := k) (K := K) X f).map g) :=
    fun g ↦ fextPullbackTransition_isAffineHom X f g
  obtain ⟨i, W, hW, hW_eq⟩ := AlgebraicGeometry.exists_preimage_eq
    (fextPullbackDiagram (k := k) (K := K) X f)
    (fextPullbackCone (k := k) (K := K) X f)
    (fextPullbackConeIsLimit (k := k) (K := K) X f) UK hUK
  let E : IntermediateField k K := i.unop.1
  let : FiniteDimensional k E := i.unop.2
  let eE : pullback f (spectrumMap k E) ≅
      (fextPullbackDiagram (k := k) (K := K) X f).obj i :=
    pullbackSymmetry f (spectrumMap k E)
  let V' : (pullback f (spectrumMap k E)).Opens := eE.hom ⁻¹ᵁ W
  let p : pullback f (spectrumMap k K) ⟶ pullback f (spectrumMap k E) :=
    eK.hom ≫ (fextPullbackCone (k := k) (K := K) X f).π.app i ≫ eE.inv
  have hq : (fextPullbackCone (k := k) (K := K) X f).π.app i ≫
      pullback.fst (spectrumMap k E) f =
        pullback.fst (spectrumMap k K) f ≫
          Spec.map (CommRingCat.ofHom (algebraMap E K)) ∧
      (fextPullbackCone (k := k) (K := K) X f).π.app i ≫
      pullback.snd (spectrumMap k E) f = pullback.snd (spectrumMap k K) f := by
    dsimp [fextPullbackCone, fextPullbackDiagram, fextOverCone, fextOverDiagram]
    simp only [Over.pullback_map_left, Over.homMk_left]
    exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨hqfst, hqsnd⟩ := hq
  have hKfst : eK.hom ≫ pullback.fst (spectrumMap k K) f =
      pullback.snd f (spectrumMap k K) := pullbackSymmetry_hom_comp_fst ..
  have hKsnd : eK.hom ≫ pullback.snd (spectrumMap k K) f =
      pullback.fst f (spectrumMap k K) := pullbackSymmetry_hom_comp_snd ..
  have hEfst : eE.inv ≫ pullback.fst f (spectrumMap k E) =
      pullback.snd (spectrumMap k E) f := pullbackSymmetry_inv_comp_fst ..
  have hEsnd : eE.inv ≫ pullback.snd f (spectrumMap k E) =
      pullback.fst (spectrumMap k E) f := pullbackSymmetry_inv_comp_snd ..
  refine ⟨E, inferInstance, V', compact_preimage_of_schemeIso eE W hW, p, ?_, ?_, ?_⟩
  · simp only [p, Category.assoc, hEfst, hqsnd, hKsnd]
  · have h1 : p ≫ pullback.snd f (spectrumMap k E) =
        eK.hom ≫ ((fextPullbackCone (k := k) (K := K) X f).π.app i ≫
          pullback.fst (spectrumMap k E) f) := by
      simp only [p, Category.assoc]
      rw [hEsnd]
    rw [h1, hqfst]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) hKfst)
  · have hpe : p ≫ eE.hom =
        eK.hom ≫ (fextPullbackCone (k := k) (K := K) X f).π.app i := by
      simp only [p, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      V = eK.hom ⁻¹ᵁ UK := by
        show V = (eK.hom ≫ eK.inv) ⁻¹ᵁ V
        simp
      _ = (eK.hom ≫ (fextPullbackCone (k := k) (K := K) X f).π.app i) ⁻¹ᵁ W := by
        rw [Scheme.Hom.comp_preimage, hW_eq]
      _ = (p ≫ eE.hom) ⁻¹ᵁ W := by rw [hpe]
      _ = p ⁻¹ᵁ V' := by rw [Scheme.Hom.comp_preimage]

/-- A quasi-compact open in the base change of a scheme to a Galois extension is fixed by an open
subgroup of the Galois group. -/
@[stacks 04KU "part (2)"]
public theorem exists_open_subgroup_fixing_isCompact_open
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (V : (pullback f (spectrumMap k K)).Opens) (hV : IsCompact V.1) :
    ∃ H : Subgroup Gal(K/k), IsOpen (H : Set Gal(K/k)) ∧
      ∀ σ : Gal(K/k), σ ∈ H →
        ∃ a : pullback f (spectrumMap k K) ≅ pullback f (spectrumMap k K),
          a.hom ≫ pullback.fst f (spectrumMap k K) = pullback.fst f (spectrumMap k K) ∧
          a.hom ≫ pullback.snd f (spectrumMap k K) =
            pullback.snd f (spectrumMap k K) ≫
              Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ∧
      V = a.hom ⁻¹ᵁ V := by
  obtain ⟨E, hE, V', hV', p, hp₁, hp₂, hV⟩ :=
    exists_finite_subextension_descending_isCompact_open X f V hV
  refine ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, fun σ hσ ↦
    ⟨galoisActionIso f σ, galoisActionIso_fst f σ, galoisActionIso_snd f σ, ?_⟩⟩
  rw [hV, ← Scheme.Hom.comp_preimage, galoisActionIso_comp_desc f E σ hσ p hp₁ hp₂]

end AlgebraicGeometry
