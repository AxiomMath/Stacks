module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StrictHenselizationOverField
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separably closed fields and henselian local rings with separably closed residue field

Two facts about separably closed fields used in the proofs of Stacks 0F0V and 0F0X.

* A separably closed field `k` has cohomological dimension zero: `Spec(k)` is the spectrum of a
  strictly henselian local ring, which has no higher étale cohomology (Stacks 03QO).
* A separable algebraic extension of fields is ind-étale: it is the directed union of its
  finite subextensions, each of which is étale.
* A separable closure of a field `F` maps into every henselian local `F`-algebra `O` whose
  residue field is separably closed. The separable closure is ind-étale over `F` and embeds over
  `F` into the residue field of `O`, and such an embedding lifts to a local map into `O`
  (Stacks 04GU). In Interlude I of the proof of Stacks 0F0V, `O` is a strict henselization.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed`:
  `cd(Spec k) ≤ 0` for `k` separably closed.
* `AlgebraicGeometry.ind_etale_of_isSeparable`: a separable algebraic extension is ind-étale.
* `AlgebraicGeometry.exists_algHom_separableClosure_of_henselianLocalRing`: the separable
  closure of `F` maps into `O`.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing IntermediateField

universe u

namespace AlgebraicGeometry

/-- The residue field of a field `K` is `K` itself. -/
private def residueRingEquiv (K : Type u) [Field K] : K ≃+* ResidueField K :=
  RingEquiv.ofBijective (residue K) ⟨(residue K).injective, residue_surjective⟩

/-- **A separable algebraic extension of fields is ind-étale.** `E` is the directed union of
its intermediate fields of finite degree over `F`, and each of these is a finite separable,
hence étale, `F`-algebra. -/
public theorem ind_etale_of_isSeparable (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] :
    (CommAlgCat.etale.{u} F).ind.{u} (CommAlgCat.of F E) := by
  rw [← StacksDraft.indEtale_iff]
  let ι := {K : IntermediateField F E // FiniteDimensional F K}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  refine StacksDraft.indEtale_of_directed_etale_subalgebras (ι := ι)
    (fun K => K.1.toSubalgebra) ?_ (fun K => ?_) ?_
  · intro K L
    have := K.2
    have := L.2
    exact ⟨⟨K.1 ⊔ L.1, inferInstance⟩, toSubalgebra_le_toSubalgebra.mpr le_sup_left,
      toSubalgebra_le_toSubalgebra.mpr le_sup_right⟩
  · have := K.2
    have : Algebra.IsSeparable F K.1 := Algebra.isSeparable_tower_bot_of_isSeparable F K.1 E
    have : Algebra.FormallyEtale F K.1 := Algebra.FormallyEtale.of_isSeparable F K.1
    have : Algebra.FinitePresentation F K.1 :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ({} : Algebra.Etale F K.1)
  · exact eq_top_iff.mpr fun x _ => Algebra.mem_iSup_of_mem (S := fun K : ι => K.1.toSubalgebra)
      (⟨F⟮x⟯, adjoin.finiteDimensional (Algebra.IsSeparable.isSeparable F x).isIntegral⟩ : ι)
      (IntermediateField.mem_adjoin_simple_self F x)

/-- **A separable closure maps into a henselian local ring with separably closed residue
field.** Let `F` be a field and `O` a henselian local `F`-algebra whose residue field is
separably closed. Then there is an `F`-algebra map from the separable closure of `F` to `O`: the
separable closure is ind-étale over `F` and embeds into the residue field of `O` over `F`, and
such an embedding lifts uniquely to a local map (Stacks 04GU). -/
public theorem exists_algHom_separableClosure_of_henselianLocalRing (F O : Type u) [Field F]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
    [Algebra F O] : Nonempty (SeparableClosure F →ₐ[F] O) := by
  let E := SeparableClosure F
  let : Algebra F (ResidueField O) := ((residue O).comp (algebraMap F O)).toAlgebra
  let g : E →ₐ[F] ResidueField O := IsSepClosed.lift
  let eE := residueRingEquiv E
  let φres : ResidueField E →+* ResidueField O := g.toRingHom.comp eE.symm.toRingHom
  have hφres : φres.comp ((residue E).comp (algebraMap F E)) =
      (residue O).comp (algebraMap F O) := by
    ext z
    change g (eE.symm (eE (algebraMap F E z))) = _
    rw [eE.symm_apply_apply, g.commutes]
    rfl
  obtain ⟨e, -, -⟩ := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
    ((CommAlgCat.etale F).ind.prop_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv.symm : E ≃ₐ[F] ULift.{u} E))
      (ind_etale_of_isSeparable F E)) φres hφres
  exact ⟨e⟩

namespace Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **A separably closed field has cohomological dimension zero.** A separably closed field is a
strictly henselian local ring, whose spectrum has no higher étale cohomology (Stacks 03QO). -/
@[sga "2 XIV 3.2" "special case"]
public theorem etaleCohomologicalDimension_spec_le_zero_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] : etaleCohomologicalDimension (Spec (.of k)) ≤ 0 := by
  have : IsSepClosed (ResidueField k) := IsSepClosed.of_ringEquiv (residueRingEquiv k).symm
  have : StrictlyHenselianLocalRing k := {}
  exact etaleCohomologicalDimension_le _ 0 fun F _ q hq =>
    Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology k F q
      (by exact_mod_cast hq)

end Scheme

end AlgebraicGeometry
