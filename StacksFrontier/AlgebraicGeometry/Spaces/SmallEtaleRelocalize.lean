module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# The small étale site does not see the base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension of
Stacks 03I5 (2), which views a presheaf `F` on the big fppf site of `W` as a presheaf on the big
fppf site of `S`; the absolute view `AlgebraicGeometry.Space.viewOverIntegers` of an algebraic
space is the case of the structure morphism of `W` to the terminal scheme.  An étale chart of
`Λ_h F` is the same thing as an étale chart of `F`: a morphism `h_U ⟶ Λ_h F` is a factorization
of the structure morphism of `U` through `W` together with a section of `F`.  So the small étale
sites of `F` and of `Λ_h F` are equivalent, by an equivalence which does not change the
underlying schemes of the charts.  Consequently the two structure sheaves correspond, the two
rings of global functions are isomorphic, and the categories of modules and of quasi-coherent
modules on the two sites are identified compatibly with global sections.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeChartsEquivalence`: the charts of `F` and of `Λ_h F` are
  equivalent categories.
* `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`: the small étale sites of `F` and of
  `Λ_h F` are equivalent, compatibly with the underlying schemes.
* `AlgebraicGeometry.Space.globalFunctionsRelocalizeEquiv`: the rings of global functions of
  `Λ_h F` and of `F` are isomorphic.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.topology_eq_inducedTopology_relocalize`: the small étale
  topology of `F` is the topology induced from that of `Λ_h F` along the equivalence.
* `AlgebraicGeometry.Space.surjective_sectionsMap_relocalize`: right exactness of global
  sections on quasi-coherent modules passes from `F` to `Λ_h F`.

## Implementation notes

The functor from charts of `F` to charts of `Λ_h F` is `AlgebraicGeometry.relocalizeChart` on the
chart morphisms and `CategoryTheory.Over.map h` on the objects, which leaves underlying schemes
and morphisms of schemes unchanged on the nose.  The inverse is built from the factorizations of
`AlgebraicGeometry.exists_relocalizeChart`; it too leaves underlying schemes unchanged on the
nose.  That matters because the covering families of the small étale sites are the *chosen*
étale coverings of the big site, a condition on the family of underlying schemes which is not
invariant under isomorphism; with both functors preserving underlying schemes on the nose, a
family is a covering exactly when its image is.

For the same reason the structure sheaf of `F` is the direct image of the structure sheaf of
`Λ_h F` along the equivalence by definition, so modules over the two structure sheaves are
compared by `Stacks.SheafOfModules.reindexEquivalence` with no change of rings.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u'} C] {C' : Type u} [Category.{u'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.inverse.IsDenseSubsite J J'] (R : Sheaf J RingCat.{w})

/-- **Right exactness of global sections on quasi-coherent modules is invariant under an
equivalence of ringed sites.** If every epimorphism of quasi-coherent modules over the
transported structure sheaf is surjective on global sections, so is every epimorphism of
quasi-coherent modules over `R`: reindexing is an equivalence of module categories, it preserves
quasi-coherence (`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex`), and global sections of a
reindexed module are those of the module, by restriction along the equivalence `e.functor`. -/
theorem surjective_sectionsMap_of_reindex
    (hX : ∀ ⦃M N : SheafOfModules.{w} (reindexRing J' e R)⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g)) :
    ∀ ⦃M N : SheafOfModules.{w} R⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g) := by
  intro M N g hg hM hN t
  let Φ := (reindexEquivalence (J' := J') e R).functor
  have hρ : ∀ P : SheafOfModules.{w} R, Function.Bijective
      (e.functor.op.sectionsPrecomp (P := P.val.presheaf ⋙ CategoryTheory.forget _)) :=
    fun P => Functor.bijective_sectionsPrecomp _ _
  obtain ⟨s', hs'⟩ := hX (Φ.map g) inferInstance (isQuasicoherentOnSite_reindex (J' := J') e R M)
    (isQuasicoherentOnSite_reindex (J' := J') e R N) (e.functor.op.sectionsPrecomp t)
  obtain ⟨s, rfl⟩ := (hρ M).2 s'
  exact ⟨s, (hρ N).1 hs'⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)

/-! ### Charts of `F` and of `Λ_h F` -/

variable {F} in
/-- Extending charts along `h` is injective: the extension of a chart is the image of the chart
under the faithful functor `Λ_h`, read through an isomorphism. -/
theorem relocalizeChart_injective {U : BigFppfOver B W hW} {a a' : yoneda.obj U ⟶ F}
    (e : relocalizeChart B W S hW hS h a = relocalizeChart B W S hW hS h a') : a = a' := by
  have _ := relocalizePresheaf_faithful h
  refine (OverShriek.relocalizePresheafFunctor h).map_injective ?_
  simpa [relocalizeChart] using e

/-- The functor from charts of `F` to charts of `Λ_h F`: a chart `a : h_U ⟶ F` goes to its
extension `AlgebraicGeometry.relocalizeChart`, a chart of `Λ_h F` on the same scheme. -/
def relocalizeChartsFunctor :
    CostructuredArrow yoneda F ⥤
      CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F) where
  obj V := CostructuredArrow.mk (relocalizeChart B W S hW hS h V.hom)
  map {V V'} g := CostructuredArrow.homMk ((Over.map h).map g.left) (by
    dsimp
    rw [relocalizeChart_naturality, CostructuredArrow.w])
  map_id V := by
    apply CostructuredArrow.hom_ext
    simp
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    simp

/-- The functor from charts of `F` to charts of `Λ_h F` is faithful. -/
instance relocalizeChartsFunctor_faithful : (relocalizeChartsFunctor B W S hW hS h F).Faithful where
  map_injective {_ _} _ _ e :=
    CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (congrArg (fun k => k.left.left) e))

/-- The functor from charts of `F` to charts of `Λ_h F` is full. -/
instance relocalizeChartsFunctor_full : (relocalizeChartsFunctor B W S hW hS h F).Full where
  map_surjective {V V'} g := by
    let φ : (Over.map h).obj V.left ⟶ (Over.map h).obj V'.left := g.left
    have hw : yoneda.map φ ≫ relocalizeChart B W S hW hS h V'.hom =
        relocalizeChart B W S hW hS h V.hom := CostructuredArrow.w g
    have hbase : φ ≫ relocalizeOverHom B W S hW hS h V'.left =
        relocalizeOverHom B W S hW hS h V.left := by
      apply yoneda.map_injective
      rw [yoneda.map_comp, ← relocalizeChart_comp_relocalizeToYoneda B W S hW hS h V'.hom,
        ← Category.assoc, hw, relocalizeChart_comp_relocalizeToYoneda]
    let k : V.left ⟶ V'.left := Over.homMk φ.left (congrArg CommaMorphism.left hbase)
    have hk : (Over.map h).map k = φ := Over.OverMorphism.ext rfl
    have hkw : yoneda.map k ≫ V'.hom = V.hom := by
      apply relocalizeChart_injective B W S hW hS h
      rw [← relocalizeChart_naturality, hk, hw]
    exact ⟨CostructuredArrow.homMk k hkw, CostructuredArrow.hom_ext _ _ hk⟩

section Inverse

variable {F}
variable (V : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- The factorization through `W` of the structure morphism of the scheme of a chart of
`Λ_h F`. -/
def relocalizeChartBase : V.left.left ⟶ B.obj hW :=
  Classical.choose (exists_relocalizeChart B W S hW hS h V.left V.hom)

/-- The factorization `relocalizeChartBase` composed with `h` is the structure morphism of the
scheme of the chart. -/
theorem relocalizeChartBase_comp : relocalizeChartBase B W S hW hS h V ≫ h = V.left.hom :=
  Classical.choose (Classical.choose_spec (exists_relocalizeChart B W S hW hS h V.left V.hom))

/-- The chart of `F` of which a chart of `Λ_h F` is the extension. -/
def relocalizeChartDescent :
    yoneda.obj (Over.mk (relocalizeChartBase B W S hW hS h V)) ⟶ F :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_relocalizeChart B W S hW hS h V.left V.hom)))

/-- The structure morphism of a chart of `Λ_h F` is the extension `relocalizeChart` of
`relocalizeChartDescent`, precomposed with the image under `yoneda` of the isomorphism
`relocalizeBaseHom` of objects over `S`. -/
theorem relocalizeChartDescent_spec :
    V.hom = yoneda.map (relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V))
        ≫
      relocalizeChart B W S hW hS h (relocalizeChartDescent B W S hW hS h V) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_relocalizeChart B W S hW hS h V.left V.hom)))

/-- A chart of `Λ_h F` is isomorphic to the extension of the chart of `F` it comes from, by an
isomorphism which is the identity on the underlying scheme. -/
def relocalizeChartsDescentIso :
    (relocalizeChartsFunctor B W S hW hS h F).obj
        (CostructuredArrow.mk (relocalizeChartDescent B W S hW hS h V)) ≅ V := by
  let ι := relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V)
  refine CostructuredArrow.isoMk (asIso ι).symm ?_
  change yoneda.map (inv ι) ≫ V.hom =
    relocalizeChart B W S hW hS h (relocalizeChartDescent B W S hW hS h V)
  conv_lhs => rw [relocalizeChartDescent_spec B W S hW hS h V]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The isomorphism `relocalizeChartsDescentIso` is the identity on the underlying scheme. -/
theorem relocalizeChartsDescentIso_hom_left_left :
    (relocalizeChartsDescentIso B W S hW hS h V).hom.left.left = 𝟙 _ :=
  inv_relocalizeBaseHom_left B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V)

/-- The inverse of `relocalizeChartsDescentIso` is the identity on the underlying scheme. -/
theorem relocalizeChartsDescentIso_inv_left_left :
    (relocalizeChartsDescentIso B W S hW hS h V).inv.left.left = 𝟙 _ :=
  relocalizeBaseHom_left B W S hW hS h (relocalizeChartBase_comp B W S hW hS h V)

end Inverse

/-- The inverse functor, from charts of `Λ_h F` to charts of `F`, built from the factorizations
of `AlgebraicGeometry.exists_relocalizeChart`.  It does not change the underlying schemes. -/
def relocalizeChartsInverse :
    CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F) ⥤
      CostructuredArrow yoneda F where
  obj V := CostructuredArrow.mk (relocalizeChartDescent B W S hW hS h V)
  map {V V'} f := (relocalizeChartsFunctor B W S hW hS h F).preimage
    ((relocalizeChartsDescentIso B W S hW hS h V).hom ≫ f ≫
      (relocalizeChartsDescentIso B W S hW hS h V').inv)
  map_id V := by
    apply (relocalizeChartsFunctor B W S hW hS h F).map_injective
    simp
  map_comp f g := by
    apply (relocalizeChartsFunctor B W S hW hS h F).map_injective
    simp

/-- The functor `relocalizeChartsInverse` does not change the underlying morphism of schemes of a
morphism of charts. -/
theorem relocalizeChartsInverse_map_left_left
    {V V' : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F)}
    (f : V ⟶ V') : ((relocalizeChartsInverse B W S hW hS h F).map f).left.left = f.left.left := by
  have e := congrArg (fun k => k.left.left)
    ((relocalizeChartsFunctor B W S hW hS h F).map_preimage
      ((relocalizeChartsDescentIso B W S hW hS h V).hom ≫ f ≫
        (relocalizeChartsDescentIso B W S hW hS h V').inv))
  simp only [CostructuredArrow.comp_left, Over.comp_left,
    relocalizeChartsDescentIso_hom_left_left, relocalizeChartsDescentIso_inv_left_left] at e
  exact e

/-- **The charts of `F` and of `Λ_h F` are equivalent.** -/
def relocalizeChartsEquivalence :
    CostructuredArrow yoneda F ≌
      CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  let G := relocalizeChartsFunctor B W S hW hS h F
  let H := relocalizeChartsInverse B W S hW hS h F
  let ε : H ⋙ G ≅ 𝟭 _ := NatIso.ofComponents (relocalizeChartsDescentIso B W S hW hS h)
    (fun f => by simp [G, H, relocalizeChartsInverse])
  CategoryTheory.Equivalence.mk G H
    (((Functor.FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
      (G.leftUnitor ≪≫ (Functor.isoWhiskerLeft G ε).symm ≪≫ (Functor.associator G H G).symm))
    ε

/-! ### The small étale sites of `F` and of `Λ_h F` -/

/-- Being an étale chart is invariant under isomorphism of charts. -/
instance isClosedUnderIsomorphisms_isEtaleChart (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (IsEtaleChart B S hS G).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => ((MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).comma_iso_iff e).mp hX⟩

/-- An étale chart of `Λ_h F` is exactly the extension of an étale chart of `F`. -/
theorem isEtaleChart_inverseImage_relocalizeChartsFunctor :
    (IsEtaleChart B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)).inverseImage
      (relocalizeChartsEquivalence B W S hW hS h F).functor = IsEtaleChart B W hW F := by
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  funext V
  exact propext (presheaf_relocalizeChart_iff B W S hW hS h
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) V.hom)

/-- **The small étale sites of `F` and of `Λ_h F` are equivalent.** -/
def SmallEtale.relocalizeEquivalence :
    SmallEtale B W hW F ≌ SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  (relocalizeChartsEquivalence B W S hW hS h F).congrFullSubcategory
    (isEtaleChart_inverseImage_relocalizeChartsFunctor B W S hW hS h F)

/-- The equivalence of small étale sites does not change the underlying schemes. -/
theorem SmallEtale.relocalizeEquivalence_functor_comp_toSchemes :
    (relocalizeEquivalence B W S hW hS h F).functor ⋙
        toSchemes B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) =
      toSchemes B W hW F := rfl

/-- The inverse equivalence does not change the underlying schemes either. -/
theorem SmallEtale.relocalizeEquivalence_inverse_comp_toSchemes :
    (relocalizeEquivalence B W S hW hS h F).inverse ⋙ toSchemes B W hW F =
      toSchemes B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  CategoryTheory.Functor.hext (fun _ => rfl)
    (fun _ _ f => heq_of_eq (relocalizeChartsInverse_map_left_left B W S hW hS h F f.hom))

/-- The functor of the equivalence of small étale sites is continuous: it carries a chosen
étale covering family to a family with the same underlying schemes. -/
instance SmallEtale.isContinuous_relocalizeEquivalence_functor :
    (relocalizeEquivalence B W S hW hS h F).functor.IsContinuous (topology B W hW F)
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) := by
  let e := relocalizeEquivalence B W S hW hS h F
  apply Functor.le_inducedTopology_iff.mp
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro U R hR
  obtain ⟨E, rfl, hE⟩ := hR
  change Sieve.generate E.presieve₀ ∈ e.functor.inducedTopology _ U
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, ← Sieve.generate_map_eq_functorPushforward,
    ← PreZeroHypercover.presieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck ⟨E.map e.functor, rfl, hE⟩

/-- The inverse of the equivalence of small étale sites is continuous. -/
instance SmallEtale.isContinuous_relocalizeEquivalence_inverse :
    (relocalizeEquivalence B W S hW hS h F).inverse.IsContinuous
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (topology B W hW F) := by
  let e := relocalizeEquivalence B W S hW hS h F
  apply Functor.le_inducedTopology_iff.mp
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro U R hR
  obtain ⟨E, rfl, hE⟩ := hR
  change Sieve.generate E.presieve₀ ∈ e.inverse.inducedTopology _ U
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, ← Sieve.generate_map_eq_functorPushforward,
    ← PreZeroHypercover.presieve₀_map]
  refine Precoverage.generate_mem_toGrothendieck ⟨E.map e.inverse, rfl, ?_⟩
  change B.etaleCovering ⟨(e.inverse ⋙ toSchemes B W hW F).obj U,
    E.map (e.inverse ⋙ toSchemes B W hW F)⟩
  rw [relocalizeEquivalence_inverse_comp_toSchemes]
  exact hE

/-- **The small étale topology of `F` is induced from that of `Λ_h F`.** -/
theorem SmallEtale.topology_eq_inducedTopology_relocalize :
    topology B W hW F = (relocalizeEquivalence B W S hW hS h F).functor.inducedTopology
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) := by
  let e := relocalizeEquivalence B W S hW hS h F
  refine le_antisymm (Functor.le_inducedTopology_iff.mpr
    (isContinuous_relocalizeEquivalence_functor B W S hW hS h F)) ?_
  intro X T hT
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hT
  have hT' := Functor.le_inducedTopology_iff.mpr
    (isContinuous_relocalizeEquivalence_inverse B W S hW hS h F) _ hT
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_equivalence_eq_pullback] at hT'
  have := (topology B W hW F).pullback_stable (e.unitIso.hom.app X) hT'
  rw [← Sieve.pullback_comp, show e.unitIso.hom.app X ≫ e.unitInv.app X = 𝟙 X from
    e.unitIso.hom_inv_id_app X] at this
  simpa using this

/-- The inverse of the equivalence of small étale sites makes the small étale site of `Λ_h F` a
dense subsite of that of `F`. -/
instance SmallEtale.isDenseSubsite_relocalizeEquivalence_inverse :
    (relocalizeEquivalence B W S hW hS h F).inverse.IsDenseSubsite
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (topology B W hW F) := by
  rw [topology_eq_inducedTopology_relocalize B W S hW hS h F]
  exact inferInstanceAs ((relocalizeEquivalence B W S hW hS h F).symm.functor.IsDenseSubsite _
    ((relocalizeEquivalence B W S hW hS h F).symm.inverse.inducedTopology _))

/-! ### Structure sheaves, global functions and modules -/

/-- The structure presheaf of `F` is the restriction of the structure presheaf of `Λ_h F` along
the equivalence of small étale sites, by definition. -/
theorem SmallEtale.relocalizeEquivalence_functor_op_comp_structurePresheaf :
    (relocalizeEquivalence B W S hW hS h F).functor.op ⋙
        structurePresheaf B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) =
      structurePresheaf B W hW F := rfl

/-- **The rings of global functions of `Λ_h F` and of `F` are isomorphic**, by restriction along
the equivalence of small étale sites. -/
def globalFunctionsRelocalizeEquiv :
    globalFunctions B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) ≃+*
      globalFunctions B W hW F :=
  RingEquiv.ofBijective
    ({ toFun := fun s => ⟨fun V => s.val
          (op ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj V.unop)),
          fun f => s.property ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.op.map f)⟩
       map_one' := Subtype.ext (funext fun _ => rfl)
       map_mul' := fun _ _ => Subtype.ext (funext fun _ => rfl)
       map_zero' := Subtype.ext (funext fun _ => rfl)
       map_add' := fun _ _ => Subtype.ext (funext fun _ => rfl) } :
      globalFunctions B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) →+*
        globalFunctions B W hW F)
    (Functor.bijective_sectionsPrecomp (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.op
      (structurePresheaf B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) ⋙
        CategoryTheory.forget CommRingCat))

/-- The isomorphism of global functions is evaluation at the charts of `F`, read as charts of
`Λ_h F`. -/
theorem globalFunctionsRelocalizeEquiv_apply
    (s : globalFunctions B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
    (V : (SmallEtale B W hW F)ᵒᵖ) :
    (globalFunctionsRelocalizeEquiv B W S hW hS h F s).val V =
      s.val (op ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj V.unop)) := rfl

variable {F} (hF : IsAlgebraicSpace B W hW F)
  (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- **Right exactness of global sections on quasi-coherent modules passes to `Λ_h F`.** An
epimorphism of quasi-coherent modules on `Λ_h F` is carried by the equivalence of small étale
sites to an epimorphism of quasi-coherent modules on `F`, with the same global sections; the
structure sheaf of `F` is the direct image of that of `Λ_h F` by definition. -/
theorem surjective_sectionsMap_relocalize
    (hX : ∀ ⦃M N : Modules.{u, u} B W hW F hF⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g)) :
    ∀ ⦃M N : Modules.{u, u} B S hS _ hF'⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g) :=
  @Stacks.SheafOfModules.surjective_sectionsMap_of_reindex _ _ _ _
    (smallEtaleRingedSite B S hS _ hF').J (smallEtaleRingedSite B W hW F hF).J
    (SmallEtale.relocalizeEquivalence B W S hW hS h F)
    (SmallEtale.isContinuous_relocalizeEquivalence_functor B W S hW hS h F)
    (SmallEtale.isContinuous_relocalizeEquivalence_inverse B W S hW hS h F)
    (SmallEtale.isDenseSubsite_relocalizeEquivalence_inverse B W S hW hS h F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS _ hF').O) hX

end AlgebraicGeometry.Space

end
