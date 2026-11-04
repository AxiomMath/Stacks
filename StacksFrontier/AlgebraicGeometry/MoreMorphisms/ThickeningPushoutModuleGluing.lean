module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout08KU
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine

/-!
# Gluing and comparing modules across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y` an affine morphism, `Y' = Y ⨿_X X'` the pushout of
[Stacks Project, Tag 07RT] and `g : V' ⟶ Y'` a morphism, with the three base changes
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`. The equivalence of
[Stacks Project, Tag 08KU] (`Stacks.Pushout.isEquivalence_flatBaseChangeTripleFunctor`) is read
here as the two statements the proof of [Stacks Project, Tag 0D44] uses about modules:

* **morphisms glue**: for quasi-coherent modules `M`, `N` on `V'` flat over `Y'`, a pair of
  morphisms between their restrictions to `V` and to `U'` agreeing on `U` is the restriction of a
  unique morphism `M ⟶ N`;
* **modules glue**: a quasi-coherent module on `V` flat over `Y`, one on `U'` flat over `X'` and
  an isomorphism of their restrictions to `U` are the restrictions of a quasi-coherent module on
  `V'` flat over `Y'`.

It also records that an invertible module on a scheme flat over a base is quasi-coherent and flat
over that base, which is what makes the two statements apply to invertible modules.

## Main results

* `Stacks.Pushout.existsUnique_hom_of_compatible`: morphisms glue.
* `Stacks.Pushout.exists_glue_of_compatible`: modules glue.
* `Stacks.Pushout.flatQuasicoherent_of_isInvertible`: an invertible module on a scheme flat over
  a base is quasi-coherent and flat over the base.

## References

* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- An invertible module is finite locally free and quasi-coherent. -/
private theorem isFiniteLocallyFree_and_isQuasicoherent_of_isInvertible {W : Scheme.{u}}
    (L : W.Modules) [AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L ∧ L.IsQuasicoherent := by
  have hL1 := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := W.toRingedSpace) L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (hM := hL1) L 1
  exact ⟨this, Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree L⟩

/-- **An invertible module on a scheme flat over a base is quasi-coherent and flat over the
base**: it is finite locally free of rank one. -/
theorem flatQuasicoherent_of_isInvertible {W S : Scheme.{u}} (h : W ⟶ S) [Flat h]
    (L : W.Modules) [AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf
      W.ringCatSheaf.2 L] :
    FlatQuasicoherent h L := by
  obtain ⟨_, _⟩ := isFiniteLocallyFree_and_isQuasicoherent_of_isInvertible L
  exact ⟨inferInstance, VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h L⟩

section Coherence

/-- Transport of a pullback along an equality of the first factor of a composite commutes with
the comparison of the composite. -/
@[reassoc]
theorem pullbackCongr_hom_app_comp_pullbackComp_hom_app {A B D : Scheme.{u}} {c₁ c₂ : A ⟶ B}
    (h : c₁ = c₂) (t : B ⟶ D) (L : D.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback t).obj L) ≫
        (Scheme.Modules.pullbackComp c₂ t).hom.app L =
      (Scheme.Modules.pullbackComp c₁ t).hom.app L ≫
        (Scheme.Modules.pullbackCongr (congrArg (· ≫ t) h)).hom.app L := by
  subst h
  rw [pullbackCongr_rfl_app, pullbackCongr_rfl_app, Category.id_comp, Category.comp_id]

/-- The associativity coherence of pullbacks, in the direction splitting off the last factor
inside the first. -/
@[reassoc]
theorem pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (N : D.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app N) ≫
        (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app N =
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫
          (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N ≫
        (Scheme.Modules.pullbackCongr (Category.assoc a b c)).hom.app N := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp a (b ≫ c)).inv.app N ≫
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app N))]
  have e1 : ((Scheme.Modules.pullbackComp a (b ≫ c)).inv.app N ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app N)) ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app N) ≫
        (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app N = 𝟙 _ := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [e1, ← Scheme.Modules.pullbackComp_assoc_inv_app a b c N]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

/-- **The comparison of two factorisations of a pullback is compatible with pulling back.** Let
`a₁ ≫ b₁ = a₂ ≫ b₂`, and let `Θ` be the identification `a₁^* b₁^* ≅ a₂^* b₂^*` built from the two
comparisons of composites. Given isomorphisms `l₁ : (b₁ ≫ t)^* L ≅ b₁^* N` and
`l₂ : (b₂ ≫ t)^* L ≅ b₂^* N` whose restrictions along `a₁` and `a₂` agree through `Θ`, the induced
morphisms `b₁^* t^* L ⟶ b₁^* N` and `b₂^* t^* L ⟶ b₂^* N` agree through `Θ`. -/
theorem pullbackComp_compatible {U V₁ V₂ W Y : Scheme.{u}} (a₁ : U ⟶ V₁) (b₁ : V₁ ⟶ W)
    (a₂ : U ⟶ V₂) (b₂ : V₂ ⟶ W) (t : W ⟶ Y) (w₀ : a₁ ≫ b₁ = a₂ ≫ b₂) (L : Y.Modules)
    (N : W.Modules)
    (l₁ : (Scheme.Modules.pullback (b₁ ≫ t)).obj L ⟶ (Scheme.Modules.pullback b₁).obj N)
    (l₂ : (Scheme.Modules.pullback (b₂ ≫ t)).obj L ⟶ (Scheme.Modules.pullback b₂).obj N)
    (h : (Scheme.Modules.pullbackComp a₁ (b₁ ≫ t)).inv.app L ≫ (Scheme.Modules.pullback a₁).map l₁ ≫
        (Scheme.Modules.pullbackComp a₁ b₁).hom.app N ≫
            (Scheme.Modules.pullbackCongr w₀).hom.app N =
      (Scheme.Modules.pullbackCongr (by rw [← Category.assoc, w₀, Category.assoc])).hom.app L ≫
        (Scheme.Modules.pullbackComp a₂ (b₂ ≫ t)).inv.app L ≫ (Scheme.Modules.pullback a₂).map l₂ ≫
          (Scheme.Modules.pullbackComp a₂ b₂).hom.app N) :
    (Scheme.Modules.pullback a₁).map ((Scheme.Modules.pullbackComp b₁ t).hom.app L ≫ l₁) ≫
        (Scheme.Modules.pullbackComp a₁ b₁).hom.app N ≫
            (Scheme.Modules.pullbackCongr w₀).hom.app N ≫
          (Scheme.Modules.pullbackComp a₂ b₂).inv.app N =
      (Scheme.Modules.pullbackComp a₁ b₁).hom.app ((Scheme.Modules.pullback t).obj L) ≫
        (Scheme.Modules.pullbackCongr w₀).hom.app ((Scheme.Modules.pullback t).obj L) ≫
          (Scheme.Modules.pullbackComp a₂ b₂).inv.app ((Scheme.Modules.pullback t).obj L) ≫
            (Scheme.Modules.pullback a₂).map ((Scheme.Modules.pullbackComp b₂ t).hom.app L ≫
                l₂) := by
  have hA₁ := pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app a₁ b₁ t L
  have hA₂ := pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app a₂ b₂ t L
  have hC := pullbackCongr_hom_app_comp_pullbackComp_hom_app w₀ t L
  have h' := (Iso.inv_comp_eq ((Scheme.Modules.pullbackComp a₁ (b₁ ≫ t)).app L)).mp h
  have hA₂' : (Scheme.Modules.pullbackComp a₂ b₂).inv.app ((Scheme.Modules.pullback t).obj L) ≫
      (Scheme.Modules.pullback a₂).map ((Scheme.Modules.pullbackComp b₂ t).hom.app L) =
      (Scheme.Modules.pullbackComp (a₂ ≫ b₂) t).hom.app L ≫
        (Scheme.Modules.pullbackCongr (Category.assoc a₂ b₂ t)).hom.app L ≫
        (Scheme.Modules.pullbackComp a₂ (b₂ ≫ t)).inv.app L := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp a₂ b₂).hom.app
      ((Scheme.Modules.pullback t).obj L)), Iso.hom_inv_id_app_assoc, ← reassoc_of% hA₂,
      Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, reassoc_of% h', Iso.app_hom, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]
  rw [reassoc_of% hA₁, Functor.map_comp, reassoc_of% hA₂', reassoc_of% hC,
    reassoc_of% pullbackCongr_trans_app, reassoc_of% pullbackCongr_trans_app]

/-- Transport of a pullback along an equality of morphisms is an `eqToHom`. -/
theorem pullbackCongr_hom_app_eq_eqToHom {A B : Scheme.{u}} {p₁ p₂ : A ⟶ B} (h : p₁ = p₂)
    (N : B.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N =
      eqToHom (congrArg (fun k : A ⟶ B ↦ (Scheme.Modules.pullback k).obj N) h) := by
  subst h
  rw [pullbackCongr_rfl_app, eqToHom_refl]

end Coherence

/-- An invertible module on a scheme is of finite presentation. -/
theorem isFinitePresentation_of_isInvertible {W : Scheme.{u}} (L : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    L.IsFinitePresentation := by
  obtain ⟨_, _⟩ := isFiniteLocallyFree_and_isQuasicoherent_of_isInvertible L
  have htf := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae L).out 4 1
  exact (htf.mp inferInstance).2

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
  [IsAffineHom f] [HasPushout i f] (g : V' ⟶ pushout i f)

omit [IsAffineHom f] in
/-- The overlap comparison of Tag 08KU followed by the comparison of the composite through `U'`
is the comparison of the composite through `V` followed by the transport between the two
composites. -/
theorem overlapComparison_hom_app_comp_pullbackComp_hom_app (M : V'.Modules) :
    (overlapComparison i f g).hom.app M ≫
        (Scheme.Modules.pullbackComp (commonToAmbient i f g) (ambientRestriction i f g)).hom.app
          M =
      (Scheme.Modules.pullbackComp (commonToTarget i f g) (targetRestriction i f g)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g)).hom.app M := by
  show ((Scheme.Modules.pullbackComp (commonToTarget i f g) (targetRestriction i f g)).hom.app M
    ≫ (Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g)).hom.app M ≫
      (Scheme.Modules.pullbackComp (commonToAmbient i f g) (ambientRestriction i f g)).inv.app M) ≫
      _ = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg _ (Category.comp_id _)

omit [IsAffineHom f] in
/-- **Restrictions along the overlap determine compatible restrictions to `V` and `U'`.** Let
`t : V' ⟶ Y`, `L` a module on `Y` and `N` a module on `V'`, and let `l₁`, `l₂` identify the
pullbacks of `L` along `V ⟶ V' ⟶ Y` and `U' ⟶ V' ⟶ Y` with the restrictions of `N`. If their
restrictions to `U` agree through the overlap comparison of `N`, then the induced morphisms
`(t^* L)|_V ⟶ N|_V` and `(t^* L)|_{U'} ⟶ N|_{U'}` are compatible through the overlap
comparisons, so that `Stacks.Pushout.existsUnique_hom_of_compatible` applies to them. -/
theorem compatible_of_overlapComparison {Y₀ : Scheme.{u}} (t : V' ⟶ Y₀) (L : Y₀.Modules)
    (N : V'.Modules)
    (l₁ : (Scheme.Modules.pullback (targetRestriction i f g ≫ t)).obj L ⟶
      (Scheme.Modules.pullback (targetRestriction i f g)).obj N)
    (l₂ : (Scheme.Modules.pullback (ambientRestriction i f g ≫ t)).obj L ⟶
      (Scheme.Modules.pullback (ambientRestriction i f g)).obj N)
    (hobj : (Scheme.Modules.pullback (commonToTarget i f g ≫ targetRestriction i f g ≫ t)).obj L =
      (Scheme.Modules.pullback (commonToAmbient i f g ≫ ambientRestriction i f g ≫ t)).obj L)
    (key : (Scheme.Modules.pullbackComp (commonToTarget i f g)
          (targetRestriction i f g ≫ t)).inv.app L ≫
        (Scheme.Modules.pullback (commonToTarget i f g)).map l₁ ≫ 𝟙 _ =
      eqToHom hobj ≫ (Scheme.Modules.pullbackComp (commonToAmbient i f g)
          (ambientRestriction i f g ≫ t)).inv.app L ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map l₂ ≫
          (overlapComparison i f g).inv.app N) :
    (Scheme.Modules.pullback (commonToTarget i f g)).map
        ((Scheme.Modules.pullbackComp (targetRestriction i f g) t).hom.app L ≫ l₁) ≫
        ((overlapComparison i f g).app N).hom =
      ((overlapComparison i f g).app ((Scheme.Modules.pullback t).obj L)).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map
          ((Scheme.Modules.pullbackComp (ambientRestriction i f g) t).hom.app L ≫ l₂) := by
  have w₀ := commonToTarget_comp_targetRestriction i f g
  have wT : commonToTarget i f g ≫ targetRestriction i f g ≫ t =
      commonToAmbient i f g ≫ ambientRestriction i f g ≫ t := by
    rw [← Category.assoc, w₀, Category.assoc]
  have hov := overlapComparison_hom_app_comp_pullbackComp_hom_app i f g N
  have k2 := key =≫ ((overlapComparison i f g).hom.app N ≫
    (Scheme.Modules.pullbackComp (commonToAmbient i f g) (ambientRestriction i f g)).hom.app N)
  nth_rewrite 1 [hov] at k2
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] at k2
  rw [← pullbackCongr_hom_app_eq_eqToHom wT L] at k2
  exact pullbackComp_compatible _ _ _ _ t w₀ L N l₁ l₂ k2

omit [IsAffineHom f] in
/-- **A glued module restricts compatibly along the two factorisations of `U ⟶ V'`.** If the
restrictions `μ : M|_V ≅ A` and `ν : M|_{U'} ≅ A'` of a module `M` on `V'` are compatible with a
comparison `θ = l₁ ≪≫ l₂⁻¹` of `A|_U` with `A'|_U` through a third module, then the two
identifications of `M|_U` with that module, through `V` and through `U'`, agree up to the
transport between the two composites `U ⟶ V'`. -/
theorem pullbackComp_inv_comp_eq_of_compatible (M : V'.Modules)
    {A : (pullback (pushout.inr i f) g).Modules} {A' : (pullback (pushout.inl i f) g).Modules}
    {K : (pullback (i ≫ pushout.inl i f) g).Modules}
    (μ : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ≅ A)
    (ν : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ≅ A')
    (l₁ : (Scheme.Modules.pullback (commonToTarget i f g)).obj A ≅ K)
    (l₂ : (Scheme.Modules.pullback (commonToAmbient i f g)).obj A' ≅ K)
    (hcomm : (Scheme.Modules.pullback (commonToTarget i f g)).map μ.hom ≫ (l₁ ≪≫ l₂.symm).hom =
      ((overlapComparison i f g).app M).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map ν.hom) :
    (Scheme.Modules.pullbackComp (commonToTarget i f g) (targetRestriction i f g)).inv.app M ≫
        (Scheme.Modules.pullback (commonToTarget i f g)).map μ.hom ≫ l₁.hom =
      eqToHom (congrArg (fun k ↦ (Scheme.Modules.pullback k).obj M)
          (commonToTarget_comp_targetRestriction i f g)) ≫
        (Scheme.Modules.pullbackComp (commonToAmbient i f g) (ambientRestriction i f g)).inv.app
          M ≫ (Scheme.Modules.pullback (commonToAmbient i f g)).map ν.hom ≫ l₂.hom := by
  have h₁ : (Scheme.Modules.pullback (commonToTarget i f g)).map μ.hom ≫ l₁.hom =
      ((overlapComparison i f g).app M).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map ν.hom ≫ l₂.hom := by
    rw [← reassoc_of% hcomm, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [h₁, ← pullbackCongr_hom_app_eq_eqToHom (commonToTarget_comp_targetRestriction i f g) M]
  show _ ≫
      ((Scheme.Modules.pullbackComp (commonToTarget i f g) (targetRestriction i f g)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g)).hom.app M ≫
        (Scheme.Modules.pullbackComp (commonToAmbient i f g)
          (ambientRestriction i f g)).inv.app M) ≫
      _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

include hi in
/-- **Morphisms of modules glue across the pushout** (Tag 08KU, full faithfulness). For
quasi-coherent modules `M` and `N` on `V'` flat over `Y'`, morphisms between their restrictions
to `V` and to `U'` which agree on `U` through the canonical identifications are the restrictions
of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_compatible {M N : V'.Modules} (hM : FlatQuasicoherent g M)
    (hN : FlatQuasicoherent g N)
    (σ : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ⟶
      (Scheme.Modules.pullback (targetRestriction i f g)).obj N)
    (τ : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ⟶
      (Scheme.Modules.pullback (ambientRestriction i f g)).obj N)
    (hστ : (Scheme.Modules.pullback (commonToTarget i f g)).map σ ≫
        ((overlapComparison i f g).app N).hom =
      ((overlapComparison i f g).app M).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map τ) :
    ∃! φ : M ⟶ N, (Scheme.Modules.pullback (targetRestriction i f g)).map φ = σ ∧
      (Scheme.Modules.pullback (ambientRestriction i f g)).map φ = τ := by
  have := isEquivalence_flatBaseChangeTripleFunctor_of_hasPushout i f g hi
  let F := flatBaseChangeTripleFunctor i f g hi
  let M' : FlatQuasicoherentModule g := ⟨M, hM⟩
  let N' : FlatQuasicoherentModule g := ⟨N, hN⟩
  let θ0 : (F.obj M').obj ⟶ (F.obj N').obj :=
    { target := σ, ambient := τ, comm := hστ }
  let θ : F.obj M' ⟶ F.obj N' := ObjectProperty.homMk θ0
  refine ⟨(F.preimage θ).hom, ?_, ?_⟩
  · have h := congrArg (fun k : F.obj M' ⟶ F.obj N' ↦ k.hom) (F.map_preimage θ)
    exact ⟨congrArg GluingTripleHom.target h, congrArg GluingTripleHom.ambient h⟩
  · rintro φ ⟨h₁, h₂⟩
    have hφ : F.map (ObjectProperty.homMk φ : M' ⟶ N') = θ := by
      ext1
      show (⟨_, _, _⟩ : GluingTripleHom _ _) = θ0
      congr
    exact congrArg (fun k : M' ⟶ N' ↦ k.hom) (F.map_injective (hφ.trans (F.map_preimage θ).symm))

include hi in
/-- **Isomorphisms of modules glue across the pushout.** The isomorphism version of
`Stacks.Pushout.existsUnique_hom_of_compatible`: isomorphisms of the restrictions to `V` and to
`U'` agreeing on `U` are the restrictions of an isomorphism `M ≅ N`. -/
theorem exists_iso_of_compatible {M N : V'.Modules} (hM : FlatQuasicoherent g M)
    (hN : FlatQuasicoherent g N)
    (σ : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ≅
      (Scheme.Modules.pullback (targetRestriction i f g)).obj N)
    (τ : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ≅
      (Scheme.Modules.pullback (ambientRestriction i f g)).obj N)
    (hστ : (Scheme.Modules.pullback (commonToTarget i f g)).map σ.hom ≫
        ((overlapComparison i f g).app N).hom =
      ((overlapComparison i f g).app M).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map τ.hom) :
    ∃ ℓ : M ≅ N, (Scheme.Modules.pullback (targetRestriction i f g)).map ℓ.hom = σ.hom ∧
      (Scheme.Modules.pullback (ambientRestriction i f g)).map ℓ.hom = τ.hom := by
  have hinv : (Scheme.Modules.pullback (commonToTarget i f g)).map σ.inv ≫
      ((overlapComparison i f g).app M).hom =
      ((overlapComparison i f g).app N).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map τ.inv := by
    rw [← cancel_mono ((Scheme.Modules.pullback (commonToAmbient i f g)).map τ.hom),
      Category.assoc, Category.assoc, ← hστ, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := existsUnique_hom_of_compatible i f hi g hM hN σ.hom τ.hom hστ
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, -⟩ := existsUnique_hom_of_compatible i f hi g hN hM σ.inv τ.inv hinv
  have hid : ∀ {K : V'.Modules} (hK : FlatQuasicoherent g K) (k : K ⟶ K),
      (Scheme.Modules.pullback (targetRestriction i f g)).map k = 𝟙 _ →
      (Scheme.Modules.pullback (ambientRestriction i f g)).map k = 𝟙 _ → k = 𝟙 K := by
    intro K hK k hk₁ hk₂
    obtain ⟨_, -, huniq⟩ := existsUnique_hom_of_compatible i f hi g hK hK (𝟙 _) (𝟙 _) (by simp)
    exact (huniq k ⟨hk₁, hk₂⟩).trans (huniq (𝟙 K) ⟨by simp, by simp⟩).symm
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ₁, hφ₂⟩
  · exact hid hM _ (by rw [Functor.map_comp, hφ₁, hψ₁, Iso.hom_inv_id])
      (by rw [Functor.map_comp, hφ₂, hψ₂, Iso.hom_inv_id])
  · exact hid hN _ (by rw [Functor.map_comp, hφ₁, hψ₁, Iso.inv_hom_id])
      (by rw [Functor.map_comp, hφ₂, hψ₂, Iso.inv_hom_id])

include hi in
/-- **Modules glue across the pushout** (Tag 08KU, essential surjectivity). A quasi-coherent
module on `V` flat over `Y`, a quasi-coherent module on `U'` flat over `X'` and an isomorphism
of their restrictions to `U` are the restrictions of a quasi-coherent module on `V'` flat over
`Y'`, compatibly with the given isomorphism. -/
theorem exists_glue_of_compatible
    (A : (pullback (pushout.inr i f) g).Modules) (A' : (pullback (pushout.inl i f) g).Modules)
    (θ : (Scheme.Modules.pullback (commonToTarget i f g)).obj A ≅
      (Scheme.Modules.pullback (commonToAmbient i f g)).obj A')
    (hA : FlatQuasicoherent (targetBase i f g) A) (hA' : FlatQuasicoherent (ambientBase i f g) A') :
    ∃ (M : V'.Modules) (μ : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ≅ A)
      (ν : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ≅ A'),
      FlatQuasicoherent g M ∧
        (Scheme.Modules.pullback (commonToTarget i f g)).map μ.hom ≫ θ.hom =
          ((overlapComparison i f g).app M).hom ≫
            (Scheme.Modules.pullback (commonToAmbient i f g)).map ν.hom := by
  have := isEquivalence_flatBaseChangeTripleFunctor_of_hasPushout i f g hi
  let F := flatBaseChangeTripleFunctor i f g hi
  let T : FlatGluingTriple i f g := ⟨⟨A, A', θ⟩, ⟨hA, hA'⟩⟩
  let E := F.objObjPreimageIso T
  let P := F.obj (F.objPreimage T)
  have hhi := congrArg (fun k : P ⟶ P ↦ k.hom.target) E.hom_inv_id
  have hih := congrArg (fun k : T ⟶ T ↦ k.hom.target) E.inv_hom_id
  have hhi' := congrArg (fun k : P ⟶ P ↦ k.hom.ambient) E.hom_inv_id
  have hih' := congrArg (fun k : T ⟶ T ↦ k.hom.ambient) E.inv_hom_id
  refine ⟨(F.objPreimage T).obj, ⟨E.hom.hom.target, E.inv.hom.target, hhi, hih⟩,
    ⟨E.hom.hom.ambient, E.inv.hom.ambient, hhi', hih'⟩, (F.objPreimage T).property,
    E.hom.hom.comm⟩

end Stacks.Pushout

end
