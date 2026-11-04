module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SpecializationClosedSupportColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZeroStalkAtGenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Étale sheaves with vanishing stalk at a generic point are colimits of constructible sheaves

Let `X` be a quasi-compact and quasi-separated scheme and let `η` be a generic point of an
irreducible component of `X`. A torsion abelian sheaf, or a sheaf of `Λ`-modules for a Noetherian
ring `Λ`, on `X_étale` whose stalk at a geometric point `η̄` above `η` vanishes is a filtered
colimit of constructible sheaves each of whose supports is contained in a closed subscheme of `X`
not containing `η`. This is Stacks 0F0M, parts (1) and (2).

## Main results

* `AlgebraicGeometry.exists_smallEtaleGeometricStalkFunctor_map_eq_zero` and
  `AlgebraicGeometry.exists_smallEtaleGeometricStalkModuleFunctor_map_eq_zero` — in a filtered
  colimit of constructible sheaves with vanishing stalk at a geometric point, every stage has a
  transition map whose stalk vanishes. This is Stacks 095P in the form the source uses it.
* `exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem_of_torsion` —
  **Stacks 0F0M (1)**.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_support_notMem` —
  **Stacks 0F0M (2)**.

## Implementation notes

The source deduces the vanishing of a transition map at `η̄` from Stacks 095P applied after
restriction to `η`. What is used here instead is the same fact read at the stalk: the geometric
stalk is a left adjoint, so it carries the colimit to a filtered colimit of groups (or modules)
with vertex zero, and the stalk of a constructible sheaf is finitely generated
(`AlgebraicGeometry.addGroupFG_smallEtaleGeometricStalk_of_isConstructibleAbelianSheaf`,
`AlgebraicGeometry.isFG_etaleStalk_of_isConstructibleModuleSheaf`), so finitely many generators
die at one stage (`CategoryTheory.Limits.exists_map_eq_zero_of_isColimit_of_isZero`).

Part (1) is the reduction
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZeroStalkAtGenericPoint` with both of
its inputs supplied: Stacks 03SA (2) for torsion abelian sheaves, in the local sense of torsion
of Stacks 0DD7, is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`. Part (2) runs the
same argument with Stacks 03SA (3), Stacks 03RZ (3) and Stacks 09YS (3).

## References

* [Stacks Project, Tag 0F0M](https://stacks.math.columbia.edu/tag/0F0M)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 005K](https://stacks.math.columbia.edu/tag/005K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.IsFiltered

/-- In a filtered category, finitely many properties of arrows out of `i`, each stable under
postcomposition and each satisfied by some arrow out of `i`, are satisfied by one arrow. -/
public theorem exists_hom_forall_of_finset {I : Type*} [Category I] [IsFiltered I] (i : I)
    {α : Type*} (S : Finset α) (P : α → ∀ {j : I}, (i ⟶ j) → Prop)
    (hP : ∀ (a : α) {j k : I} (f : i ⟶ j) (g : j ⟶ k), P a f → P a (f ≫ g))
    (h : ∀ a ∈ S, ∃ (j : I) (f : i ⟶ j), P a f) :
    ∃ (j : I) (f : i ⟶ j), ∀ a ∈ S, P a f := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | insert a S _ ih =>
    obtain ⟨j, f, hf⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨k, g, hg⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨l, f', g', hfg⟩ := IsFiltered.span f g
    refine ⟨l, f ≫ f', fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · rw [hfg]
      exact hP _ g g' hg
    · exact hP _ f f' (hf b hb)

end CategoryTheory.IsFiltered

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasZeroMorphisms C]

/-- **A finitely generated term of a filtered diagram with zero colimit dies at a finite stage.**
Let `K` be a filtered diagram in a concrete category whose forgetful functor preserves its
colimit, and let `c` be a colimit cocone with zero vertex. If `S` is a finite subset of `K i`
such that a morphism out of `K i` is determined by its values on `S`, then some transition map
out of `K i` is zero. -/
public theorem exists_map_eq_zero_of_isColimit_of_isZero {I : Type*} [Category I] [IsFiltered I]
    {K : I ⥤ C} [PreservesColimit K (forget C)] {c : Cocone K} (hc : IsColimit c)
    (hz : IsZero c.pt) (i : I) (S : Finset (ToType (K.obj i)))
    (hS : ∀ {Y : C} (g h : K.obj i ⟶ Y), (∀ x ∈ S, g x = h x) → g = h) :
    ∃ (j : I) (f : i ⟶ j), K.map f = 0 := by
  obtain ⟨j, f, hf⟩ := IsFiltered.exists_hom_forall_of_finset i S
    (fun x {j} (f : i ⟶ j) => K.map f x = (0 : K.obj i ⟶ K.obj j) x)
    (fun x {j k} f g (hx : K.map f x = (0 : K.obj i ⟶ K.obj j) x) => by
      rw [K.map_comp, ConcreteCategory.comp_apply, hx, ← ConcreteCategory.comp_apply,
        zero_comp])
    (fun x _ => by
      have hrep : c.ι.app i x = c.ι.app i ((0 : K.obj i ⟶ K.obj i) x) := by
        rw [← ConcreteCategory.comp_apply, zero_comp, hz.eq_of_tgt (c.ι.app i) 0]
      obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq K hc x _ hrep
      refine ⟨k, f, ?_⟩
      rw [hfg, ← ConcreteCategory.comp_apply, zero_comp])
  exact ⟨j, f, hS _ _ hf⟩

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **The geometric stalks of a constructible abelian sheaf are finitely generated.** -/
public theorem addGroupFG_smallEtaleGeometricStalk_of_isConstructibleAbelianSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (p : GeometricPoint X.obj) :
    AddGroup.FG ((smallEtaleGeometricStalkFunctor B X p).obj F) := by
  let e := AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B ℤ f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B ℤ
  have hQ := isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF
  have hfg := isFG_etaleStalk_of_isConstructibleModuleSheaf.{u, 0} B ℤ X _ hQ p
  have iso : etaleStalk B X.obj X.property p
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.obj X.property) e).functor.obj
        F).obj ≅ e.functor.obj ((smallEtaleGeometricStalkFunctor B X p).obj F) :=
    ((geometricPointSitePoint B X.obj X.property p).sheafFiberCompIso e.functor).app F
  rw [ModuleCat.isFG_iff] at hfg
  have : Module.Finite ℤ (e.functor.obj ((smallEtaleGeometricStalkFunctor B X p).obj F)) :=
    Module.Finite.equiv iso.toLinearEquiv
  have hfg' : AddGroup.FG (e.functor.obj ((smallEtaleGeometricStalkFunctor B X p).obj F)) :=
    Module.Finite.iff_addGroup_fg.mp (by convert this; exact Subsingleton.elim _ _)
  have : AddGroup.FG ((e.functor ⋙ e.inverse).obj
      ((smallEtaleGeometricStalkFunctor B X p).obj F)) := hfg'
  exact AddGroup.fg_of_surjective
    (f := (e.unitIso.inv.app ((smallEtaleGeometricStalkFunctor B X p).obj F)).hom)
    (ConcreteCategory.bijective_of_isIso
      (e.unitIso.inv.app ((smallEtaleGeometricStalkFunctor B X p).obj F))).2

/-- **Stacks 095P at a geometric point, for abelian sheaves.** Let `ℱ = colim Dᵢ` be a filtered
colimit of constructible abelian sheaves on `X_étale` whose stalk at a geometric point `p` is
zero. Then out of every stage `i` there is a transition map `Dᵢ ⟶ Dⱼ` whose stalk at `p` is
zero.

The stalk at `p` is a left adjoint, so it carries the colimit to a colimit of abelian groups with
vertex zero; the stalk of `Dᵢ` is a finitely generated abelian group, and each of finitely many
generators dies at some stage. This is how the source applies Stacks 095P in the proof of
Stacks 0F0M, there after restricting to the point under `p`. -/
public theorem exists_smallEtaleGeometricStalkFunctor_map_eq_zero
    (p : GeometricPoint X.obj)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (ι : D ⟶ (Functor.const I).obj ℱ) (hc : IsColimit (Cocone.mk ℱ ι))
    (hD : ∀ i, IsConstructibleAbelianSheaf B X (D.obj i))
    (hstalk : IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ)) (i : I) :
    ∃ (j : I) (f : i ⟶ j), (smallEtaleGeometricStalkFunctor B X p).map (D.map f) = 0 := by
  classical
  let S := smallEtaleGeometricStalkFunctor B X p
  obtain ⟨T, hT⟩ := (addGroupFG_smallEtaleGeometricStalk_of_isConstructibleAbelianSheaf
    B X (D.obj i) (hD i) p).out
  exact exists_map_eq_zero_of_isColimit_of_isZero (K := D ⋙ S)
    (isColimitOfPreserves S hc) hstalk i T
    fun g h hgh => ConcreteCategory.hom_ext _ _ fun x => DFunLike.congr_fun
      (AddMonoidHom.eq_of_eqOn_dense hT (f := g.hom) (g := h.hom) hgh) x

/-- **Stacks 0F0M (1).** Let `X` be a quasi-compact and quasi-separated scheme and let `η` be a
generic point of an irreducible component of `X`. Let `ℱ` be a torsion abelian sheaf on `X_étale`
whose stalk at a geometric point `η̄` above `η` is zero. Then `ℱ` is a filtered colimit of
constructible abelian sheaves, each of whose supports is contained in a closed subset of `X` —
equivalently a closed subscheme of `X` — not containing `η`.

Torsion is the local condition of Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`. This is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem` with its
two inputs proved: Stacks 03SA (2) is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`, and Stacks 095P
in the form the source uses is
`AlgebraicGeometry.exists_smallEtaleGeometricStalkFunctor_map_eq_zero`. -/
@[stacks 0F0M "part (1), torsion abelian sheaves, torsion in the local sense of Stacks 0DD7"]
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem_of_torsion
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (η : X.obj) (hη : η ∈ genericPoints X.obj)
    (p : GeometricPoint X.obj) (hp : GeometricPoint.LiesOver p η)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hℱ : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) ℱ)
    (hstalk : IsZero ((smallEtaleGeometricStalkFunctor B X p).obj ℱ)) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (G : J ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (κ : G ⟶ (Functor.const J).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ κ)) ∧
        (∀ j, IsConstructibleAbelianSheaf B X (G.obj j)) ∧
          ∀ j, ∃ Z : Set X.obj, IsClosed Z ∧ η ∉ Z ∧
            supportSheaf.{u, u + 1} B X.obj X.property (G.obj j) ⊆ Z :=
  exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem B X η hη p hp ℱ hstalk
    (exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X ℱ hℱ)
    fun I _ _ D ι hc hD hz i =>
      exists_smallEtaleGeometricStalkFunctor_map_eq_zero B X p ℱ I D ι hc hD hz i

section Modules

variable (Λ : Type (u + 1)) [CommRing Λ]

private instance hasLimitsOfSize_moduleCat : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The stalk at a geometric point as a functor on sheaves of `Λ`-modules on the small étale site:
the fibre functor of the point of the site attached to the geometric point. Objectwise it is
`AlgebraicGeometry.etaleStalk`. -/
public abbrev smallEtaleGeometricStalkModuleFunctor (p : GeometricPoint X.obj) :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ⥤
      ModuleCat.{u + 1} Λ :=
  (geometricPointSitePoint B X.obj X.property p).sheafFiber (A := ModuleCat.{u + 1} Λ)

/-- **The geometric stalk of the image of a morphism of sheaves of `Λ`-modules whose geometric
stalk vanishes, vanishes**, stated for an arbitrary epi-mono factorisation `f = e ≫ m`. The stalk
functor carries `e` to an epimorphism, being a left adjoint, and `m` to a monomorphism, geometric
stalks being filtered colimits in a category satisfying AB5. -/
public theorem isZero_etaleStalk_of_moduleStalk_map_eq_zero (p : GeometricPoint X.obj)
    {F K G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (e : F ⟶ K) (m : K ⟶ G) [Epi e] [Mono m]
    (hf : (smallEtaleGeometricStalkModuleFunctor B X Λ p).map (e ≫ m) = 0) :
    IsZero (etaleStalk B X.obj X.property p K.obj) := by
  let S := smallEtaleGeometricStalkModuleFunctor B X Λ p
  let FtoP := sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)
  let St := etaleStalkPresheafFunctor B X.obj X.property p (ModuleCat.{u + 1} Λ)
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1} Λ)
  have : HasExactColimitsOfShape
      (geometricPointFiber B X.obj X.property p).Elementsᵒᵖ (ModuleCat.{u + 1} Λ) :=
    hasExactColimitsOfShape_of_final (ModuleCat.{u + 1} Λ)
      (FinallySmall.fromFilteredFinalModel.{u}
        ((geometricPointFiber B X.obj X.property p).Elementsᵒᵖ))
  have : PreservesFiniteLimits St := by
    dsimp [St, etaleStalkPresheafFunctor]
    infer_instance
  have : Mono (FtoP.map m) := (sheafToPresheaf _ _).map_mono _
  have hmono : Mono (S.map m) := preserves_mono_of_preservesLimit St (FtoP.map m)
  have hepi : Epi (S.map e) := S.map_epi _
  have hzero : S.map m = 0 := zero_of_epi_comp (S.map e) (by rw [← Functor.map_comp, hf])
  refine (IsZero.iff_id_eq_zero (S.obj K)).2 ?_
  rw [← cancel_mono (S.map m), Category.id_comp, hzero, zero_comp]

variable [IsNoetherianRing Λ]

/-- **Stacks 095P at a geometric point, for sheaves of `Λ`-modules.** Let `Λ` be a Noetherian ring
and let `ℱ = colim Dᵢ` be a filtered colimit of constructible sheaves of `Λ`-modules on `X_étale`
whose stalk at a geometric point `p` is zero. Then out of every stage `i` there is a transition
map `Dᵢ ⟶ Dⱼ` whose stalk at `p` is zero: the stalk of `Dᵢ` is a finitely generated `Λ`-module,
and each of finitely many generators dies at some stage. -/
public theorem exists_smallEtaleGeometricStalkModuleFunctor_map_eq_zero
    (p : GeometricPoint X.obj)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (ι : D ⟶ (Functor.const I).obj ℱ) (hc : IsColimit (Cocone.mk ℱ ι))
    (hD : ∀ i, IsConstructibleModuleSheaf B X Λ (D.obj i))
    (hstalk : IsZero ((smallEtaleGeometricStalkModuleFunctor B X Λ p).obj ℱ)) (i : I) :
    ∃ (j : I) (f : i ⟶ j),
      (smallEtaleGeometricStalkModuleFunctor B X Λ p).map (D.map f) = 0 := by
  classical
  let S := smallEtaleGeometricStalkModuleFunctor B X Λ p
  have hfg := isFG_etaleStalk_of_isConstructibleModuleSheaf.{u, u + 1} B Λ X _ (hD i) p
  rw [ModuleCat.isFG_iff] at hfg
  obtain ⟨T, hT⟩ := hfg.fg_top
  exact exists_map_eq_zero_of_isColimit_of_isZero (K := D ⋙ S)
    (isColimitOfPreserves S hc) hstalk i T
    fun g h hgh => ConcreteCategory.hom_ext _ _ fun x => LinearMap.congr_fun
      (LinearMap.ext_on hT (f := g.hom) (g := h.hom) hgh) x

/-- **Stacks 0F0M (2).** Let `X` be a quasi-compact and quasi-separated scheme, let `η` be a
generic point of an irreducible component of `X` and let `Λ` be a Noetherian ring. Let `ℱ` be a
sheaf of `Λ`-modules on `X_étale` whose stalk at a geometric point `η̄` above `η` is zero. Then
`ℱ` is a filtered colimit of constructible sheaves of `Λ`-modules, each of whose supports is
contained in a closed subset of `X` — equivalently a closed subscheme of `X` — not containing
`η`.

The proof is the source's proof of part (1), which it says carries over verbatim. Write
`ℱ = colim ℱᵢ` with `ℱᵢ` constructible by Stacks 03SA (3); out of every `i` choose a transition
map `ℱᵢ ⟶ ℱ_{i'(i)}` whose stalk at `η̄` vanishes, by Stacks 095P in the stalkwise form
`AlgebraicGeometry.exists_smallEtaleGeometricStalkModuleFunctor_map_eq_zero`; the images of these
transition maps form a filtered system with colimit `ℱ`
(`CategoryTheory.Limits.isColimitArrowImageCocone`), each image is constructible by Stacks 03RZ
and has vanishing stalk at `η̄`, its support is constructible by Stacks 09YS (3), and the closure
of a constructible set avoiding the generic point `η` avoids `η`. -/
@[stacks 0F0M "part (2), sheaves of modules over a Noetherian ring"]
public theorem exists_isFilteredColimit_isConstructibleModuleSheaf_support_notMem
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (η : X.obj) (hη : η ∈ genericPoints X.obj)
    (p : GeometricPoint X.obj) (hp : GeometricPoint.LiesOver p η)
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hstalk : IsZero (etaleStalk B X.obj X.property p ℱ.obj)) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (G : J ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
      (κ : G ⟶ (Functor.const J).obj ℱ),
      Nonempty (IsColimit (Cocone.mk ℱ κ)) ∧
        (∀ j, IsConstructibleModuleSheaf B X Λ (G.obj j)) ∧
          ∀ j, ∃ Z : Set X.obj, IsClosed Z ∧ η ∉ Z ∧ supportModuleSheaf B X Λ (G.obj j) ⊆ Z := by
  classical
  have hspec : SpectralSpace X.obj :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace X.obj
  let : HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) :=
    inferInstance
  let : Abelian (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :=
    inferInstance
  have hSerre := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X Λ
  obtain ⟨I, hI, hIfiltered, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs B X Λ ℱ
  let S := smallEtaleGeometricStalkModuleFunctor B X Λ p
  choose n φ hφ using exists_smallEtaleGeometricStalkModuleFunctor_map_eq_zero B X Λ p ℱ I D ι
    hc hD hstalk
  set P : ObjectProperty (Arrow I) := fun a => S.map (D.map a.hom) = 0
  have hφ' : ∀ i, P (Arrow.mk (φ i)) := hφ
  have : IsFiltered P.FullSubcategory := isFiltered_arrowFullSubcategory P φ hφ'
  obtain ⟨hcolim⟩ := isColimitArrowImageCocone P D φ hφ' hc
  have hconstr : ∀ a : P.FullSubcategory,
      IsConstructibleModuleSheaf B X Λ (Limits.image (D.map a.obj.hom)) := fun a =>
    ObjectProperty.prop_of_iso
      (P := fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) =>
        IsConstructibleModuleSheaf B X Λ F)
      (Abelian.imageIsoImage (D.map a.obj.hom))
      (ObjectProperty.prop_kernel _ (cokernel.π (D.map a.obj.hom)) (hD _)
        (ObjectProperty.prop_cokernel _ (D.map a.obj.hom) (hD _) (hD _)))
  refine ⟨P.FullSubcategory, inferInstance, inferInstance, arrowImageDiagram P D,
    (arrowImageCocone P D (Cocone.mk ℱ ι)).ι, ⟨hcolim⟩, hconstr, fun a => ?_⟩
  have hzero : IsZero (etaleStalk B X.obj X.property p (Limits.image (D.map a.obj.hom)).obj) :=
    isZero_etaleStalk_of_moduleStalk_map_eq_zero B X Λ p (factorThruImage (D.map a.obj.hom))
      (Limits.image.ι (D.map a.obj.hom)) (by rw [Limits.image.fac]; exact a.property)
  have hnot : η ∉ supportModuleSheaf B X Λ (Limits.image (D.map a.obj.hom)) := by
    rintro ⟨t, ht, hnz⟩
    exact hnz (((etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property (ht.trans hp.symm)
      (ModuleCat.{u + 1} Λ)).app (Limits.image (D.map a.obj.hom)).obj).isZero_iff.mpr hzero)
  refine ⟨closure (supportModuleSheaf B X Λ (Limits.image (D.map a.obj.hom))), isClosed_closure,
    Topology.notMem_closure_of_mem_genericPoints_of_isConstructible hη
      (isConstructible_support_moduleSheaf.{u + 1, u, u + 1} B X Λ _ (hconstr a)) hnot,
    subset_closure⟩

end Modules

end AlgebraicGeometry
