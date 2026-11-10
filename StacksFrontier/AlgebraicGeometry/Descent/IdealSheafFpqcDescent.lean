module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ImmersionLocalRepresentatives
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending ideal sheaves along an fpqc covering

Let `{q i : U i ⟶ B}` be an fpqc covering and let `J i` be an ideal sheaf on `U i` for every
`i`, such that the two pullbacks of `J i` and `J j` to `U i ×_B U j` agree. Then there is an ideal
sheaf `K` on `B` whose pullback to each `U i` is `J i`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_fpqc`: the descended ideal sheaf.

## Implementation notes

The closed subschemes cut out by the `J i` are local representatives, in the sense of
`Stacks.Flatness.localRepresentativeDescentData'`, of the property of a scheme `V` over `B` that
every base change `V ×_B U j ⟶ U j` lands in the closed subscheme of `J j`; so they form a descent
datum whose components are closed immersions. That datum is effective by Stacks 03I0
(`AlgebraicGeometry.DescentData.isFamilyEffective_of_isClosedImmersion`), the descended morphism
is a closed immersion because being one is fpqc local on the target (Stacks 02L6), and `K` is its
kernel.

## References

* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A morphism lands in the closed subscheme of an ideal sheaf exactly when the pullback of the
ideal sheaf along it is zero. -/
theorem comap_eq_bot_iff_exists {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = ⊥ ↔ ∃ g : X ⟶ I.subscheme, g ≫ I.subschemeι = f := by
  constructor
  · intro h
    have : IsIso (pullback.fst f I.subschemeι) :=
      IsClosedImmersion.isIso_iff_ker_eq_bot.mpr h
    exact ⟨inv (pullback.fst f I.subschemeι) ≫ pullback.snd f I.subschemeι, by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩
  · rintro ⟨g, rfl⟩
    rw [comap_comp, show I.comap I.subschemeι = ⊥ from ?_, comap_bot]
    change (pullback.fst I.subschemeι I.subschemeι).ker = ⊥
    have := isIso_fst_of_mono I.subschemeι
    exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- Pulling back along `a ≫ f` instead of `f` is compatible with the projections to the fibre
product. -/
private theorem exists_pullback_map_comp {A B S T : Scheme.{u}} (a : T ⟶ A) (f : A ⟶ B)
    (g : S ⟶ B) : ∃ φ : pullback (a ≫ f) g ⟶ pullback f g,
      φ ≫ pullback.fst f g = pullback.fst (a ≫ f) g ≫ a ∧
        φ ≫ pullback.snd f g = pullback.snd (a ≫ f) g :=
  ⟨pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _) (by simp [pullback.condition]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- Given ideal sheaves `J i` on the members of a family `q i : U i ⟶ B` whose pullbacks to the
pairwise fibre products agree, a morphism `t : T ⟶ U i` pulls `J i` back to zero exactly when every
base change of `t ≫ q i` along `q j` pulls `J j` back to zero. -/
private theorem forall_comap_pullbackSnd_eq_bot_iff {B : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (q : ∀ i, U i ⟶ B) (J : ∀ i, (U i).IdealSheafData)
    (hJ : ∀ i j, (J i).comap (pullback.fst (q i) (q j)) = (J j).comap (pullback.snd (q i) (q j)))
    (i : ι) {T : Scheme.{u}} (t : T ⟶ U i) :
    (∀ j, (J j).comap (pullback.snd (t ≫ q i) (q j)) = ⊥) ↔ (J i).comap t = ⊥ := by
  constructor
  · intro h
    let l : T ⟶ pullback (t ≫ q i) (q i) := pullback.lift (𝟙 _) t (by simp)
    have hl : l ≫ pullback.snd (t ≫ q i) (q i) = t := pullback.lift_snd _ _ _
    rw [← hl, comap_comp, h i, comap_bot]
  · intro ht j
    obtain ⟨φ, hφ', hφ⟩ := exists_pullback_map_comp t (q i) (q j)
    rw [← hφ, comap_comp, ← hJ i j, ← comap_comp, hφ', comap_comp, ht, comap_bot]

/-- **Ideal sheaves descend along fpqc coverings.** Let `{q i : U i ⟶ B}` be an fpqc covering
and let `J i` be ideal sheaves on the `U i` whose pullbacks to the pairwise fibre products agree.
Then there is an ideal sheaf on `B` pulling back to each `J i`. -/
@[sga "1 VIII 1.9" "partial"]
theorem exists_comap_eq_of_fpqc {B : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}}
    (q : ∀ i, U i ⟶ B) (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage B)
    (J : ∀ i, (U i).IdealSheafData)
    (hJ : ∀ i j, (J i).comap (pullback.fst (q i) (q j)) = (J j).comap (pullback.snd (q i) (q j))) :
    ∃ K : B.IdealSheafData, ∀ i, K.comap (q i) = J i := by
  let P : Over B → Prop := fun V ↦ ∀ j, (J j).comap (pullback.snd V.hom (q j)) = ⊥
  have hP : ∀ {T T' : Over B}, (T' ⟶ T) → P T → P T' := by
    intro T T' a hT j
    obtain ⟨φ, -, hφ⟩ := exists_pullback_map_comp a.left T.hom (q j)
    rw [← Over.w a, ← hφ, comap_comp, hT j, comap_bot]
  let W : ∀ i, Over (U i) := fun i ↦ Over.mk (J i).subschemeι
  have hW : ∀ i, Mono (W i).hom := fun i ↦ inferInstanceAs (Mono (J i).subschemeι)
  have h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i) :=
    fun i T ↦ (forall_comap_pullbackSnd_eq_bot_iff q J hJ i T.hom).trans <|
      (comap_eq_bot_iff_exists _ _).trans
        ⟨fun ⟨g, hg⟩ ↦ ⟨Over.homMk g hg⟩, fun ⟨g⟩ ↦ ⟨g.left, Over.w g⟩⟩
  have hWc : ∀ i, IsClosedImmersion (W i).hom := fun i ↦
    inferInstanceAs (IsClosedImmersion (J i).subschemeι)
  let d := Stacks.Flatness.localRepresentativeDescentData' P hP q W h
  obtain ⟨Z, ⟨e⟩⟩ := DescentData.isFamilyEffective_of_isClosedImmersion q hq d hWc
  let ei (i : I) : (Over.pullback (q i)).obj Z ≅ W i :=
    (eqToIso ((canonicalFamilyDescentFunctor q).obj Z i)).symm ≪≫
      (DescentData.evaluation i).mapIso e
  have hw (i : I) : (ei i).hom.left ≫ (J i).subschemeι = pullback.snd Z.hom (q i) :=
    Over.w (ei i).hom
  have hiso (i : I) : IsIso (ei i).hom.left := Functor.map_isIso (Over.forget (U i)) (ei i).hom
  have hZ : IsClosedImmersion Z.hom := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := @IsClosedImmersion) hq ?_
    rintro V' g' _ ⟨i⟩
    rw [← hw i]
    infer_instance
  refine ⟨Z.hom.ker, fun i ↦ ?_⟩
  rw [← ker_fst_of_isClosedImmersion]
  have hsw : pullback.fst (q i) Z.hom =
      (pullbackSymmetry (q i) Z.hom).hom ≫ (ei i).hom.left ≫ (J i).subschemeι := by
    rw [hw i]
    simp
  rw [hsw, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

end AlgebraicGeometry.Scheme.IdealSheafData

end
