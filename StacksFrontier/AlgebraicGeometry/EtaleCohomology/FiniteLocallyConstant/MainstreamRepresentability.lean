module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally constant sheaves of sets on Mathlib's small étale site are representable

Stacks 03RV — a finite locally constant sheaf of sets on `X_étale` is represented by a scheme
finite étale over `X` — is proved in this library on the size-bounded small étale site of
Stacks 021B (`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`).
This file transports it to Mathlib's small étale site `X.smallEtaleTopology`, along the dense
subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`.

The transport needs one general fact about dense subsites: restricting a finite locally constant
sheaf of sets along a fully faithful dense subsite inclusion gives a finite locally constant
sheaf. Its proof localizes the dense subsite at an object
(`CategoryTheory.Functor.isDenseSubsite_overPost_of_fullyFaithful`) and compares constant sheaves
along the localized inclusion.

## Main results

* `CategoryTheory.Functor.isDenseSubsite_overPost_of_fullyFaithful` — localizing a fully faithful
  dense subsite inclusion at an object gives a dense subsite inclusion.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPushforwardContinuous` — restriction along a
  fully faithful dense subsite inclusion preserves finite local constancy of sheaves of sets.
* `Stacks.EtaleCohomology.exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant` — Stacks
  03RV on Mathlib's small étale site.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)

/-- **Localizing a fully faithful dense subsite inclusion.** If `G : C ⥤ D` is fully faithful and
exhibits `(C, J)` as a dense subsite of `(D, K)`, then for every object `W` of `C` the functor
`Over.post G : C/W ⥤ D/G(W)` exhibits the localized site `(C/W, J/W)` as a dense subsite of
`(D/G(W), K/G(W))`. -/
theorem isDenseSubsite_overPost_of_fullyFaithful [G.IsDenseSubsite J K] [G.Full] [G.Faithful]
    (W : C) :
    (Over.post (X := W) G).IsDenseSubsite (J.over W) (K.over (G.obj W)) := by
  have := IsDenseSubsite.isCoverDense J K G
  have hcd : (Over.post (X := W) G).IsCoverDense (K.over (G.obj W)) := by
    refine ⟨fun T ↦ ?_⟩
    rw [GrothendieckTopology.mem_over_iff]
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K T.left)
    rintro Z f ⟨h⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨{ obj := Over.mk (G.preimage (h.map ≫ T.hom))
             lift := Over.homMk h.lift (by
               show h.lift ≫ G.map (G.preimage (h.map ≫ T.hom)) = f ≫ T.hom
               rw [G.map_preimage, ← Category.assoc, h.fac])
             map := Over.homMk h.map (by
               show h.map ≫ T.hom = G.map (G.preimage (h.map ≫ T.hom))
               exact (G.map_preimage _).symm)
             fac := by
               ext
               exact h.fac }⟩
  exact
    { isCoverDense' := hcd
      functorPushforward_mem_iff := by
        intro V S
        rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
          Sieve.overEquiv_functorPushforward_post]
        exact G.functorPushforward_mem_iff J K }

end CategoryTheory.Functor

/-! ### Finite local constancy of sheaves of sets along a dense subsite -/

namespace Stacks.ConstantSheaf

universe u' v'

variable {C : Type u'} [Category.{v'} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] [G.Full] [G.Faithful]

/-- **Pointwise transport of a constant trivialization of a sheaf of sets** along a fully
faithful dense subsite inclusion `G`: if `F` is constant over `G(W)`, its restriction along `G` is
constant over `W`, with the same value. -/
theorem nonempty_overPullback_sheafPushforwardContinuous (F : Sheaf K (Type max u' v')) (W : C)
    (E : Type max u' v')
    (h : Nonempty ((constantSheaf (K.over (G.obj W)) (Type max u' v')).obj E ≅
      (K.overPullback (Type max u' v') (G.obj W)).obj F)) :
    Nonempty ((constantSheaf (J.over W) (Type max u' v')).obj E ≅
      (J.overPullback (Type max u' v') W).obj
        ((G.sheafPushforwardContinuous (Type max u' v') J K).obj F)) := by
  have := Functor.isDenseSubsite_overPost_of_fullyFaithful J K G W
  let Φ := (Over.post (X := W) G).sheafPushforwardContinuous (Type max u' v')
    (J.over W) (K.over (G.obj W))
  have hconst : Φ.obj ((constantSheaf (K.over (G.obj W)) (Type max u' v')).obj E) ≅
      (constantSheaf (J.over W) (Type max u' v')).obj E :=
    ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (J.over W) (K.over (G.obj W))
      (Over.post (X := W) G) (Type max u' v')).app ((Functor.const (Over (G.obj W))ᵒᵖ).obj E)).symm
  obtain ⟨δ⟩ := h
  exact ⟨hconst.symm ≪≫ Φ.mapIso δ⟩

variable [HasPullbacks D]

/-- **Finite local constancy of sheaves of sets along a dense subsite**: the restriction of a
finite locally constant sheaf of sets along a fully faithful dense subsite inclusion is finite
locally constant. -/
theorem isFiniteLocallyConstant_sheafPushforwardContinuous (F : Sheaf K (Type max u' v'))
    [IsFiniteLocallyConstant K F] :
    IsFiniteLocallyConstant J ((G.sheafPushforwardContinuous (Type max u' v') J K).obj F) := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  have := Functor.IsDenseSubsite.isLocallyFull J K G
  refine ⟨fun U ↦ ?_⟩
  let T : Sieve (G.obj U) :=
    { arrows := fun Y _ ↦ ∃ E : Type max u' v', Finite E ∧
        Nonempty ((constantSheaf (K.over Y) (Type max u' v')).obj E ≅
          (K.overPullback (Type max u' v') Y).obj F)
      downward_closed := fun {_ _ _} ⟨E, hE, ⟨δ⟩⟩ k ↦ ⟨E, hE,
        ⟨Localization.overPullbackIsoOfMap K (Type max u' v') k F E δ⟩⟩ }
  have hT : T ∈ K (G.obj U) := by
    obtain ⟨I, V, f, hcov, h⟩ := ‹IsFiniteLocallyConstant K F›.exists_finite_cover (G.obj U)
    refine K.superset_covering ?_ hcov
    rintro Y g ⟨Z, k, g', ⟨i⟩, rfl⟩
    exact T.downward_closed (h i) k
  have hS : T.functorPullback G ∈ J U := (G.functorPushforward_mem_iff J K).1
    (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨T, hT⟩)
  refine ⟨Σ W : C, {f : W ⟶ U // (T.functorPullback G) f}, fun a ↦ a.1, fun a ↦ a.2.1, ?_,
    fun a ↦ ?_⟩
  · exact J.superset_covering (fun W f hf ↦ Sieve.ofArrows_mk _
      (fun a : Σ W : C, {f : W ⟶ U // (T.functorPullback G) f} ↦ a.2.1) ⟨W, f, hf⟩) hS
  · obtain ⟨E, hE, hδ⟩ := a.2.2
    exact ⟨E, hE, nonempty_overPullback_sheafPushforwardContinuous J K G F a.1 E hδ⟩

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 03RV] on Mathlib's small étale site.** A finite locally constant sheaf of sets
on `X_étale` is isomorphic to the sheaf represented by an étale `X`-scheme whose structure
morphism is finite.

The library proves this on the size-bounded small étale site of Stacks 021B
(`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`); it is
transported here along the dense subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`,
whose pushforward of sheaves is fully faithful and carries the representable sheaf of an object
of the bounded site to the representable sheaf of its image. -/
@[sga "4 IX 2.2"]
theorem exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology P] :
    ∃ V : X.Etale, IsFinite V.hom ∧
      Nonempty (P ≅ X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) := by
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  let G := SmallEtale.toEtaleSite B X hXB
  let push := G.sheafPushforwardContinuous (Type (u + 1)) (SmallEtale.topology B X hXB)
    X.smallEtaleTopology
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X hXB)
      (push.obj P) :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPushforwardContinuous _ _ G _
  obtain ⟨U, hUfin, ⟨φ⟩⟩ :=
    (isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨X, hXB⟩ (push.obj P)).1 this
  let hG : G.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful G
  let e : push.obj (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (G.obj U)) ≅
      (SmallEtale.topology B X hXB).uliftYoneda.{u + 1}.obj U :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
      (fun W => (Equiv.ulift.trans (hG.homEquiv.symm.trans Equiv.ulift.symm)).toIso)
      (fun {W W'} g => by
        ext ⟨a⟩
        apply ULift.ext
        apply hG.map_injective
        show G.map (hG.preimage (G.map g.unop ≫ a)) = G.map (g.unop ≫ hG.preimage a)
        rw [hG.map_preimage, G.map_comp, hG.map_preimage]))
  exact ⟨G.obj U, hUfin, ⟨push.preimageIso
    (φ ≪≫ sheafifiedYonedaIsoUliftYoneda _ U ≪≫ e.symm)⟩⟩

end Stacks.EtaleCohomology

end
