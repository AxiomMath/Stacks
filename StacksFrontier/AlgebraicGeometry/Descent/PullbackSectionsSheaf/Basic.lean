module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.HomPresheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# The sheaf condition for the pullback-sections presheaf

Let `F` be a quasi-coherent module on a scheme `S`. Under the hypothesis
`AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms` that morphisms of quasi-coherent modules
descend along fpqc covering families, the presheaf on the schemes over `S` sending `T ⟶ S` to
`Γ(T, T^* F)` is a sheaf for the Zariski, étale, smooth, syntomic, fppf and fpqc topologies.

## Main definitions

* `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`: for every fpqc covering family of a scheme,
  pulling morphisms of quasi-coherent modules back to the family is a bijection onto the
  morphisms of the associated descent data.

## Main results

* `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc`,
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_zariski`,
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_etale`,
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_smooth`,
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_syntomic` and
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fppf`: the sheaf condition for the
  pullback-sections presheaf, for each of these topologies.
* `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms_of_fullyFaithful` and
  `AlgebraicGeometry.nonempty_fullyFaithful_of_fpqcDescentOfQuasicoherentHoms`: the hypothesis
  is equivalent to the full faithfulness of `AlgebraicGeometry.canonicalDescentFunctor` for every
  fpqc covering family.

## Implementation notes

The index type of the covering family in `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms` is
`Type (u + 1)`, the universe in which `CategoryTheory.Presieve.exists_eq_ofArrows` presents a
presieve of `Scheme.{u}`.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Descent of morphisms of quasi-coherent modules along fpqc covering families: for every
fpqc covering family `f i : X i ⟶ S` and all quasi-coherent modules `M` and `N` on `S`, pulling
morphisms `M ⟶ N` back along the family is a bijection onto the morphisms of the associated
descent data. -/
def FpqcDescentOfQuasicoherentHoms : Prop :=
  ∀ ⦃S : Scheme.{u}⦄ ⦃I : Type (u + 1)⦄ ⦃X : I → Scheme.{u}⦄ (f : ∀ i, X i ⟶ S),
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S →
    ∀ M N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      Function.Bijective
        (((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
          modulePullbackPseudofunctor.toDescentData f).map : (M ⟶ N) → _)

/-- The action on morphisms of the composite of the inclusion of the quasi-coherent modules with
`CategoryTheory.Pseudofunctor.toDescentData` is the composite of the two actions. -/
lemma ι_comp_toDescentData_map {S : Scheme.{u}} {I : Type*} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S)
    (M N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
        modulePullbackPseudofunctor.toDescentData f).map (X := M) (Y := N) =
      (modulePullbackPseudofunctor.toDescentData f).map ∘
        (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map := rfl

/-- If the canonical
descent functor on quasi-coherent modules is fully faithful for every fpqc covering family, then
morphisms of quasi-coherent modules descend along fpqc covering families. -/
theorem fpqcDescentOfQuasicoherentHoms_of_fullyFaithful
    (h : ∀ ⦃S : Scheme.{u}⦄ ⦃I : Type (u + 1)⦄ ⦃X : I → Scheme.{u}⦄ (f : ∀ i, X i ⟶ S),
      Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S →
      Nonempty (canonicalDescentFunctor f).FullyFaithful) :
    FpqcDescentOfQuasicoherentHoms.{u} := by
  intro S I X f hfpqc M N
  let hFF : (canonicalDescentFunctor f).FullyFaithful := Classical.choice (h f hfpqc)
  let DQ := fun D : modulePullbackPseudofunctor.DescentData f => ∀ i, (D.obj i).IsQuasicoherent
  have hι : (ObjectProperty.ι DQ).FullyFaithful := ObjectProperty.fullyFaithfulι DQ
  have hcomp : Function.Bijective
      ((canonicalDescentFunctor f ⋙ ObjectProperty.ι DQ).map (X := M) (Y := N)) :=
    (hι.map_bijective ((canonicalDescentFunctor f).obj M)
      ((canonicalDescentFunctor f).obj N)).comp (hFF.map_bijective M N)
  rwa [canonicalDescentFunctor_comp_ι f] at hcomp

/-- If morphisms of quasi-coherent modules descend along fpqc covering families, then the
canonical descent functor on quasi-coherent modules is fully faithful for every fpqc covering
family. -/
theorem nonempty_fullyFaithful_of_fpqcDescentOfQuasicoherentHoms
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) {S : Scheme.{u}} {I : Type (u + 1)}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor (hd f hfpqc)

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, for quasi-coherent modules `M`
and `N` and an fpqc covering family `f`, the action of
`CategoryTheory.Pseudofunctor.toDescentData f` on morphisms `M ⟶ N` is bijective. -/
theorem bijective_toDescentData_map_of_fpqcDescent
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) {S : Scheme.{u}} {I : Type (u + 1)}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((modulePullbackPseudofunctor.toDescentData f).map : (M ⟶ N) → _) := by
  have hcomp := hd f hf ⟨M, inferInstance⟩ ⟨N, inferInstance⟩
  rw [ι_comp_toDescentData_map] at hcomp
  exact (Function.Bijective.of_comp_iff
      ((modulePullbackPseudofunctor.toDescentData f).map : (M ⟶ N) → _)
      ((ObjectProperty.fullyFaithfulι
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).map_bijective
          ⟨M, inferInstance⟩ ⟨N, inferInstance⟩)).1 hcomp

variable {S : Scheme.{u}}

private theorem isSheafFor_presheafHom_base (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (R : Presieve S) (hR : R ∈ Scheme.fpqcPrecoverage.{u} S)
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 S))).symm (Sieve.generate R)).arrows := by
  obtain ⟨I, X, f, rfl⟩ := R.exists_eq_ofArrows
  have h := (Pseudofunctor.bijective_toDescentData_map_iff
    (F := modulePullbackPseudofunctor) f M N).mp
    (bijective_toDescentData_map_of_fpqcDescent hd f hR M N)
  rw [Presieve.isSheafFor_iff_generate] at h
  convert h using 2
  apply (Sieve.overEquiv (Over.mk (𝟙 S))).injective
  show (Sieve.overEquiv (Over.mk (𝟙 S)))
    ((Sieve.overEquiv (Over.mk (𝟙 S))).symm (Sieve.ofArrows X f)) =
    (Sieve.overEquiv (Over.mk (𝟙 S)))
      (Sieve.ofArrows (fun i => Over.mk (f i)) (fun i => Over.homMk (f i)))
  rw [OrderIso.apply_symm_apply, Sieve.overEquiv_ofArrows]
  rfl

private theorem isSheafFor_presheafHom (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (T : Over S) (R : Presieve T.left)
    (hR : R ∈ Scheme.fpqcPrecoverage.{u} T.left)
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv T).symm (Sieve.generate R)).arrows := by
  obtain ⟨T, a, rfl⟩ := T.mk_surjective
  have h := isSheafFor_presheafHom_base hd R hR
    ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback a).obj N)
  change Presieve.IsSheafFor
    (modulePullbackPseudofunctor.presheafHom
      ((modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M)
      ((modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj N))
    ((Sieve.overEquiv (Over.mk (𝟙 T))).symm (Sieve.generate R)).arrows at h
  rw [← Presieve.isSheafFor_iff_of_iso
    (modulePullbackPseudofunctor.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert h using 2
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left,
      Over.homMk (𝟙 _) (by simpa using Over.w f), hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    simp at fac
    show (Sieve.generate R).arrows b.left
    simpa [fac] using (Sieve.generate R).downward_closed h d.left

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the presheaf on the schemes
over `S` sending `T ⟶ S` to the morphisms `T^* M ⟶ T^* N` is a sheaf for the fpqc
topology. -/
theorem isSheaf_presheafHom (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (modulePullbackPseudofunctor.presheafHom M N) := by
  rw [isSheaf_iff_isSheaf_of_type,
    show Scheme.fpqcTopology.{u} = Scheme.fpqcPrecoverage.{u}.toGrothendieck from rfl,
    over_toGrothendieck_eq_toGrothendieck_comap_forget,
    ← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Presieve.isSheaf_pretopology]
  intro T R hR
  simp only [Precoverage.toPretopology_toPrecoverage, Precoverage.mem_comap_iff,
    Over.forget_obj] at hR
  rw [Presieve.isSheafFor_iff_generate]
  have h := isSheafFor_presheafHom hd T _ hR M N
  convert h using 2
  apply (Sieve.overEquiv T).injective
  simp [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward]

private theorem isSheaf_over_of_le {C : Type*} [Category* C]
    {A : Type*} [Category* A] {J K : GrothendieckTopology C}
    (h : J ≤ K) (X : C) (F : (Over X)ᵒᵖ ⥤ A)
    (hF : Presheaf.IsSheaf (K.over X) F) : Presheaf.IsSheaf (J.over X) F :=
  Presheaf.IsSheaf.of_le (fun Y _ hR => h Y.left hR) hF

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every fpqc covering. -/
theorem quasiCoherentPresheaf_isSheaf_fpqc (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  Presheaf.isSheaf_of_isSheaf_comp (Scheme.fpqcTopology.over S)
    (quasiCoherentPresheafFunctor S F) (CategoryTheory.forget AddCommGrpCat)
    ((Presheaf.isSheaf_of_iso_iff (quasiCoherentPresheafIsoPresheafHom F)).mpr
      (isSheaf_presheafHom hd (Scheme.unitModule S) F))

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every Zariski covering. -/
theorem quasiCoherentPresheaf_isSheaf_zariski (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_over_of_le Scheme.zariskiTopology_le_fpqcTopology S _
    (quasiCoherentPresheaf_isSheaf_fpqc hd S F)

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every étale covering. -/
theorem quasiCoherentPresheaf_isSheaf_etale (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_over_of_le
    (Precoverage.toGrothendieck_mono Scheme.etalePrecoverage_le_fpqcPrecoverage) S _
    (quasiCoherentPresheaf_isSheaf_fpqc hd S F)

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every smooth covering. -/
theorem quasiCoherentPresheaf_isSheaf_smooth (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf ((Scheme.grothendieckTopology (@Smooth)).over S)
      (quasiCoherentPresheafFunctor S F) :=
  isSheaf_over_of_le
    (Precoverage.toGrothendieck_mono Scheme.smoothPrecoverage_le_fpqcPrecoverage) S _
    (quasiCoherentPresheaf_isSheaf_fpqc hd S F)

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every syntomic covering. -/
theorem quasiCoherentPresheaf_isSheaf_syntomic (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf ((Scheme.grothendieckTopology (@Syntomic)).over S)
      (quasiCoherentPresheafFunctor S F) :=
  isSheaf_over_of_le
    (Precoverage.toGrothendieck_mono Scheme.syntomicPrecoverage_le_fpqcPrecoverage) S _
    (quasiCoherentPresheaf_isSheaf_fpqc hd S F)

/-- Under `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the pullback-sections presheaf of
a quasi-coherent module satisfies the sheaf condition for every fppf covering. -/
theorem quasiCoherentPresheaf_isSheaf_fppf (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_over_of_le Scheme.fppfTopology_le_fpqcTopology S _
    (quasiCoherentPresheaf_isSheaf_fpqc hd S F)

end AlgebraicGeometry

end
