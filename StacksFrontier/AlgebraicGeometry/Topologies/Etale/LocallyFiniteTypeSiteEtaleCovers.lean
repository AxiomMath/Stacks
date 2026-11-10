module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSite

/-!
# Covering sieves of the locally-finite-type étale site contain étale covers

Let `S` be a scheme and `C` the category of schemes locally of finite type over `S`, with the
étale topology `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.topology` (the coarsest topology
containing the sieves whose image generates an étale covering sieve of schemes). A sieve `R` on
an object `V` of `C` is covering if and only if every point of `V` lies in the image of an étale
morphism `Z ⟶ V` of `C` belonging to `R`.

The direction "covering implies étale point cover" is an induction over the generation of the
topology: the generating sieves contain étale covers because an étale covering of the
underlying scheme of `V` consists of schemes locally of finite type over `S`; the property is
stable under pullback because the base change of an étale morphism is étale, and fibre products
of schemes locally of finite type over `S` are again locally of finite type over `S`; and it is
stable under the local character axiom by composing étale morphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.HasEtalePointCover`: every point of `V` is
  in the image of an étale morphism belonging to the sieve.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.pullbackObj`: the fibre product of two
  morphisms of `C`, computed in schemes.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.mem_topology_iff_hasEtalePointCover`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable {S : Scheme.{u}}

/-- A sieve `R` on an object `V` of the locally-finite-type étale site has an étale point cover
when every point of `V` lies in the image of an étale morphism of the site belonging to `R`. -/
def HasEtalePointCover {V : LocallyFiniteTypeEtale S} (R : Sieve V) : Prop :=
  ∀ x : V.obj.left, ∃ (Z : LocallyFiniteTypeEtale S) (f : Z ⟶ V),
    Etale ((forget S).map f) ∧ x ∈ Set.range ((forget S).map f).base ∧ R.arrows f

/-- A sieve with an étale point cover is a covering sieve. -/
theorem mem_topology_of_hasEtalePointCover {V : LocallyFiniteTypeEtale S} {R : Sieve V}
    (hR : HasEtalePointCover R) : R ∈ topology S V := by
  choose Z f het hx hR using hR
  refine (topology S).superset_covering ?_
    (mem_topology_of_etale_of_surjective Z f het (fun x ↦ ⟨x, hx x⟩))
  rw [Sieve.generate_le_iff]
  rintro W g ⟨x⟩
  exact hR x

/-- A morphism of the site whose target is locally of finite type over `S` through `X` is
itself locally of finite type. -/
instance locallyOfFiniteType_forget_map {X Z : LocallyFiniteTypeEtale S} (f : Z ⟶ X) :
    LocallyOfFiniteType ((forget S).map f) := by
  have : LocallyOfFiniteType Z.obj.hom := Z.property
  have : LocallyOfFiniteType ((forget S).map f ≫ X.obj.hom) := by
    change LocallyOfFiniteType (f.hom.left ≫ X.obj.hom)
    rw [Over.w f.hom]
    infer_instance
  exact locallyOfFiniteType_of_comp _ X.obj.hom

/-- The fibre product `Y ×_X Z` of two morphisms of the site, computed in schemes. -/
def pullbackObj {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    LocallyFiniteTypeEtale S :=
  ⟨Over.mk (pullback.fst ((forget S).map g) ((forget S).map f) ≫ Y.obj.hom), by
    change LocallyOfFiniteType (pullback.fst ((forget S).map g) ((forget S).map f) ≫ Y.obj.hom)
    have : LocallyOfFiniteType Y.obj.hom := Y.property
    infer_instance⟩

/-- The first projection of the fibre product. -/
def pullbackFst {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    pullbackObj g f ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst ((forget S).map g) ((forget S).map f)) rfl)

/-- The second projection of the fibre product. -/
def pullbackSnd {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    pullbackObj g f ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (pullback.snd ((forget S).map g) ((forget S).map f)) (by
    change pullback.snd ((forget S).map g) ((forget S).map f) ≫ Z.obj.hom =
      pullback.fst ((forget S).map g) ((forget S).map f) ≫ Y.obj.hom
    rw [← Over.w f.hom, ← Over.w g.hom]
    change pullback.snd ((forget S).map g) ((forget S).map f) ≫ (forget S).map f ≫ X.obj.hom =
      pullback.fst ((forget S).map g) ((forget S).map f) ≫ (forget S).map g ≫ X.obj.hom
    rw [pullback.condition_assoc]))

/-- The underlying morphism of schemes of `pullbackFst g f` is the first projection
`pullback.fst`. -/
@[simp]
lemma forget_map_pullbackFst {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    (forget S).map (pullbackFst g f) = pullback.fst ((forget S).map g) ((forget S).map f) :=
  rfl

/-- The underlying morphism of schemes of `pullbackSnd g f` is the second projection
`pullback.snd`. -/
@[simp]
lemma forget_map_pullbackSnd {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    (forget S).map (pullbackSnd g f) = pullback.snd ((forget S).map g) ((forget S).map f) :=
  rfl

/-- The fibre product square commutes. -/
lemma pullbackFst_comp {X Y Z : LocallyFiniteTypeEtale S} (g : Y ⟶ X) (f : Z ⟶ X) :
    pullbackFst g f ≫ g = pullbackSnd g f ≫ f := by
  apply (forget S).map_injective
  simp only [Functor.map_comp, forget_map_pullbackFst, forget_map_pullbackSnd]
  exact pullback.condition

/-- The étale point covers of the identity. -/
lemma hasEtalePointCover_top (V : LocallyFiniteTypeEtale S) :
    HasEtalePointCover (⊤ : Sieve V) := fun x ↦
  ⟨V, 𝟙 V, by rw [CategoryTheory.Functor.map_id]; infer_instance, ⟨x, by simp⟩, trivial⟩

/-- The base change of an étale morphism of schemes is étale. -/
private lemma etale_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : AlgebraicGeometry.Etale g) : AlgebraicGeometry.Etale (pullback.fst f g) :=
  inferInstance

/-- Étale point covers are stable under pullback. -/
lemma HasEtalePointCover.pullback {X Y : LocallyFiniteTypeEtale S} {R : Sieve X}
    (hR : HasEtalePointCover R) (g : Y ⟶ X) : HasEtalePointCover (R.pullback g) := by
  intro y
  obtain ⟨Z, f, het, ⟨z, hz⟩, hf⟩ := hR (((forget S).map g).base y)
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (forget S).map g) (g := (forget S).map f) y z hz.symm
  refine ⟨pullbackObj g f, pullbackFst g f, ?_, ⟨p, hp⟩, ?_⟩
  · rw [forget_map_pullbackFst]
    exact etale_pullback_fst _ _ het
  · change R.arrows (pullbackFst g f ≫ g)
    rw [pullbackFst_comp]
    exact R.downward_closed hf _

/-- Étale point covers satisfy the local character axiom. -/
lemma HasEtalePointCover.transitive {X : LocallyFiniteTypeEtale S} {R R' : Sieve X}
    (hR : HasEtalePointCover R)
    (h : ∀ ⦃Y : LocallyFiniteTypeEtale S⦄ ⦃f : Y ⟶ X⦄, R f → HasEtalePointCover (R'.pullback f)) :
    HasEtalePointCover R' := by
  intro x
  obtain ⟨Z, f, het, ⟨z, rfl⟩, hf⟩ := hR x
  obtain ⟨W, g, hget, ⟨w, rfl⟩, hg⟩ := h hf z
  refine ⟨W, g ≫ f, ?_, ⟨w, by simp⟩, hg⟩
  rw [Functor.map_comp]
  infer_instance

/-- The generating sieves of the topology have étale point covers. -/
lemma hasEtalePointCover_generate {X : LocallyFiniteTypeEtale S} {P : Presieve X}
    (hP : P ∈ Precoverage.comap (forget S) Scheme.etaleTopology.toPrecoverage X) :
    HasEtalePointCover (Sieve.generate P) := by
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff] at hP
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hP
  intro x
  obtain ⟨j, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  obtain ⟨T, h, g, hp, hfac⟩ := h𝒰 _ _ (Presieve.ofArrows.mk j)
  rcases hp with ⟨hp⟩
  rename_i Y q
  let Zj : LocallyFiniteTypeEtale S :=
    ⟨Over.mk (𝒰.f j ≫ X.obj.hom), by
      change LocallyOfFiniteType (𝒰.f j ≫ X.obj.hom)
      have : LocallyOfFiniteType X.obj.hom := X.property
      infer_instance⟩
  let k : Zj ⟶ Y := ObjectProperty.homMk (Over.homMk h (by
    change h ≫ Y.obj.hom = 𝒰.f j ≫ X.obj.hom
    rw [← hfac, ← Over.w q.hom]
    rfl))
  have e : (forget S).map (k ≫ q) = 𝒰.f j := hfac
  exact ⟨Zj, k ≫ q, e ▸ 𝒰.map_prop j, ⟨y, by rw [e]; exact hy⟩, ⟨Y, k, q, hp, rfl⟩⟩

/-- **Every covering sieve of the locally-finite-type étale site has an étale point cover.** -/
theorem hasEtalePointCover_of_mem_topology {V : LocallyFiniteTypeEtale S} {R : Sieve V}
    (hR : R ∈ topology S V) : HasEtalePointCover R := by
  change Precoverage.Saturate _ V R at hR
  induction hR with
  | of X P hP => exact hasEtalePointCover_generate hP
  | top X => exact hasEtalePointCover_top X
  | pullback X R _ Y g ih => exact ih.pullback g
  | transitive X R R' _ _ ih1 ih2 => exact ih1.transitive ih2

/-- **A sieve of the locally-finite-type étale site is covering if and only if every point is in
the image of an étale morphism of the site belonging to it.** -/
theorem mem_topology_iff_hasEtalePointCover {V : LocallyFiniteTypeEtale S} (R : Sieve V) :
    R ∈ topology S V ↔ HasEtalePointCover R :=
  ⟨hasEtalePointCover_of_mem_topology, mem_topology_of_hasEtalePointCover⟩

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
