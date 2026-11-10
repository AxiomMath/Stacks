module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion

/-!
# The stalks of the direct image with compact support, its exactness and its direct sums

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `ȳ` be a geometric
point of `Y` and let `F` be an abelian sheaf on the small étale site of `X`. The stalk of the
direct image with compact support `f_!F` at `ȳ` is the direct sum of the stalks of `F` over the
geometric points of `X` lying over `ȳ`, naturally in `F`; and `f_!` is an exact functor which
commutes with arbitrary direct sums. This is Stacks 0F5F.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekStalkIso` — the stalk decomposition
  `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekStalkIso_comp_sheafification` — the decomposition is the
  canonical map: composed with the comparison coming from the sheafification unit it is the germ
  decomposition of the finite-support direct image.
* `AlgebraicGeometry.SmallEtale.fShriekStalkIso_natural` — the decomposition is natural in the
  sheaf.
* `AlgebraicGeometry.SmallEtale.fShriekFunctor_exact` — `f_!` is exact.
* `AlgebraicGeometry.SmallEtale.fShriekFunctor_preservesCoproductsOfShape` — `f_!` commutes with
  arbitrary direct sums.

## Implementation notes

The stalk decomposition is the composite of two isomorphisms already available: sheafification
does not change a stalk, which identifies the stalk of `f_!F` with the stalk of the finite-support
direct image presheaf `f_{p!}F`, and the germ decomposition of that stalk is an isomorphism, which
is Stacks 0F6P.

Exactness is deduced from the decomposition and not proved directly. The stalk functors at the
geometric points of `Y` are jointly faithful on abelian sheaves, so they reflect colimits; the
composite of `f_!` with such a stalk functor is, by the decomposition, the direct sum over the
geometric fibre of the stalk functors of `X`, and both the stalk functors and the direct sum
preserve colimits. That gives preservation of all colimits, in particular of finite ones and of
direct sums. Preservation of finite limits then follows from preservation of finite colimits
together with preservation of monomorphisms, which is the injectivity half of the same
decomposition.

## References

* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v w

namespace AlgebraicGeometry.SmallEtale

section Decomposition

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0F5F, part (1).** The stalk of the direct image with compact support `f_!F` of a
locally quasi-finite morphism at a geometric point `ȳ` of `Y` is the direct sum of the stalks of
`F` over the geometric points of `X` lying over `ȳ`: `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. -/
@[stacks 0F5F "part (1), stalk decomposition"]
public def fShriekStalkIso (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    etaleStalk B Y.obj Y.property s ((fShriekFunctor.{u, v} B f).obj F).obj ≅
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) :=
  etaleStalkFShriekFunctorIso.{u, v} B f s F ≪≫
    finiteSupportStalkIso.{u, max (u + 1) v} B f s F fun _ => inferInstance

/-- **Stacks 0F5F, part (1).** The stalk decomposition of `f_!F` is the canonical one: the
comparison of the stalk of `f_!F` with the stalk of the finite-support direct image presheaf
`f_{p!}F`, which is induced by the sheafification unit, carries it to the germ decomposition of
Stacks 0F6P. -/
@[stacks 0F5F "part (1), canonical comparison"]
public theorem fShriekStalkIso_comp_sheafification (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    colim.map (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).1.obj F))) ≫
      (fShriekStalkIso.{u, v} B f s F).hom =
      (finiteSupportStalkIso.{u, max (u + 1) v} B f s F fun _ => inferInstance).hom :=
  (etaleStalkFShriekFunctorIso.{u, v} B f s F).inv_hom_id_assoc _

/-- **Stacks 0F5F, part (1).** The stalk decomposition of the direct image with compact support is
natural in the abelian sheaf: a morphism of sheaves on `X` acts on the direct sum of stalks over
the geometric fibre by its maps on those stalks. -/
@[stacks 0F5F "part (1), functoriality"]
public theorem fShriekStalkIso_natural (s : GeometricPoint Y.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    colim.map (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
        ((fShriekFunctor.{u, v} B f).map φ).1) ≫ (fShriekStalkIso.{u, v} B f s G).hom =
      (fShriekStalkIso.{u, v} B f s F).hom ≫
        AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s φ) := by
  have hΘ : etaleStalkSheafificationMap B Y.obj Y.property s
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj F) ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
          ((fShriekFunctor.{u, v} B f).map φ).1) =
      colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).1.map φ)) ≫
        etaleStalkSheafificationMap B Y.obj Y.property s
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).1.obj G) := by
    have h := congrArg
      (etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map
      (toSheafify_naturality (J := SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.map φ))
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h.symm
  refine (cancel_epi (etaleStalkSheafificationMap B Y.obj Y.property s
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj F))).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (fShriekStalkIso.{u, v} B f s G).hom) hΘ).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => colim.map (Functor.whiskerLeft
              (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
              ((finiteSupportPushforward.{u, max (u + 1) v} B f
                (fun _ => inferInstance)).1.map φ)) ≫ z)
            (fShriekStalkIso_comp_sheafification.{u, v} B f s G)).trans
          ((finiteSupportStalkToFiberStalks_natural B f s (fun _ => inferInstance) φ).trans
            ((congrArg (fun z => z ≫ AddCommGrpCat.ofHom
                  (fiberStalksMap.{u, max (u + 1) v} B f s φ))
                (fShriekStalkIso_comp_sheafification.{u, v} B f s F).symm).trans
              (Category.assoc _ _ _))))))

end Decomposition

section Exactness

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The stalk at a geometric point of a monomorphism of abelian étale sheaves is a
monomorphism: the stalk functor is the fibre functor of a point of the site, which is left
exact. -/
private theorem mono_etaleStalk_map (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ G)
    [Mono φ] :
    Mono (colim.map (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B S hS s)).op φ.1)) := by
  have hfil : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v}
  have hab : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  have hm : Mono (((geometricPointSitePoint B S hS s).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) v})).map φ) := Functor.map_mono _ _
  exact hm

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- A monomorphism of abelian sheaves on `X` induces an injective map on the direct sums of
stalks over the geometric fibre. -/
private theorem fiberStalksMap_injective (s : GeometricPoint Y.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) [Mono φ] :
    Function.Injective (fiberStalksMap.{u, max (u + 1) v} B f s φ) := by
  have h : Function.Injective (DirectSum.map fun x : GeometricFiberPoint B f s =>
      (colim.map (Functor.whiskerLeft (Functor.Elements.π
        (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op φ.1)).hom) := by
    refine (DirectSum.map_injective _).mpr fun x => ?_
    exact (AddCommGrpCat.mono_iff_injective _).mp
      (mono_etaleStalk_map B X.obj X.property (x.toGeometricPoint B f s) φ)
  exact h

/-- **The direct image with compact support preserves monomorphisms.** On stalks it is the
direct sum of the stalk maps over the geometric fibre, and a direct sum of injective maps is
injective; the stalks at the geometric points of `Y` jointly reflect monomorphisms. -/
private theorem fShriekFunctor_preservesMonomorphisms :
    (fShriekFunctor.{u, v} B f).PreservesMonomorphisms := by
  refine ⟨fun {F G} φ hmono => ?_⟩
  have hfib : ∀ s : GeometricPoint Y.obj,
      Mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekFunctor.{u, v} B f).map φ)) := by
    intro s
    have hm : Mono (AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s φ)) :=
      (AddCommGrpCat.mono_iff_injective _).2 (fiberStalksMap_injective B f s φ)
    have hnat := fShriekStalkIso_natural.{u, v} B f s φ
    have hcomp : Mono (colim.map (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
        ((fShriekFunctor.{u, v} B f).map φ).1) ≫ (fShriekStalkIso.{u, v} B f s G).hom) := by
      rw [hnat]
      exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _
        (Iso.isIso_hom (fShriekStalkIso.{u, v} B f s F))) hm
    exact mono_of_mono (colim.map (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
      ((fShriekFunctor.{u, v} B f).map φ).1)) (fShriekStalkIso.{u, v} B f s G).hom
  have := hfib
  exact (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Y.obj
    Y.property).jointlyReflectMonomorphisms.mono _

/-- The cofan of a family of abelian groups given by the inclusions into their direct sum. -/
private def stalkSumCofan {ι : Type u} (A : ι → AddCommGrpCat.{max (u + 1) v}) : Cofan A := by
  classical
  exact Cofan.mk (AddCommGrpCat.of (⨁ i : ι, (A i : Type _)))
    (fun i => AddCommGrpCat.ofHom (DirectSum.of (fun i => (A i : Type _)) i))

/-- The direct sum of a family of abelian groups is their coproduct. -/
private def stalkSumCofan_isColimit {ι : Type u} (A : ι → AddCommGrpCat.{max (u + 1) v}) :
    IsColimit (stalkSumCofan A) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t => AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun i => (t.inj i).hom)) ?_ ?_
  · intro t i
    ext x
    exact DirectSum.toAddMonoid_of (fun i => (t.inj i).hom) i x
  · intro t m hm
    ext x
    have h : m.hom =
        (DirectSum.toAddMonoid (fun i => (t.inj i).hom) :
          (⨁ i : ι, (A i : Type _)) →+ t.pt) := by
      refine DirectSum.addHom_ext fun i y => ?_
      have hi' := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (hm i)) y
      change m.hom ((DirectSum.of (fun i => (A i : Type _)) i) y) = (t.inj i).hom y at hi'
      rw [DirectSum.toAddMonoid_of]
      exact hi'
    exact DFunLike.congr_fun h x

/-- The direct sum of a family of abelian groups, identified with its coproduct. -/
private def stalkSumIso {ι : Type u} (A : ι → AddCommGrpCat.{max (u + 1) v}) :
    AddCommGrpCat.of (⨁ i : ι, (A i : Type _)) ≅ ∐ A :=
  IsColimit.coconePointUniqueUpToIso (stalkSumCofan_isColimit A) (coproductIsCoproduct A)

/-- The identification of a direct sum with the coproduct carries the inclusion of a summand to
the inclusion of a factor of the coproduct. -/
private theorem stalkSumIso_hom_ι {ι : Type u} (A : ι → AddCommGrpCat.{max (u + 1) v}) (i : ι) :
    (stalkSumCofan A).inj i ≫ (stalkSumIso A).hom = Sigma.ι A i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (stalkSumCofan_isColimit A) (coproductIsCoproduct A) ⟨i⟩

/-- The identification of a direct sum with the coproduct is natural in the family. -/
private theorem stalkSumIso_natural {ι : Type u} (A A' : ι → AddCommGrpCat.{max (u + 1) v})
    (g : ∀ i, A i ⟶ A' i) :
    AddCommGrpCat.ofHom (DirectSum.map fun i => (g i).hom) ≫ (stalkSumIso A').hom =
      (stalkSumIso A).hom ≫ Limits.Sigma.map g := by
  classical
  refine (stalkSumCofan_isColimit A).hom_ext fun j => ?_
  obtain ⟨i⟩ := j
  have hmap : (stalkSumCofan A).inj i ≫
      AddCommGrpCat.ofHom (DirectSum.map fun j => (g j).hom) =
      g i ≫ (stalkSumCofan A').inj i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    exact DirectSum.map_of (fun j => (g j).hom) i x
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (stalkSumIso A').hom) hmap).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => g i ≫ z) (stalkSumIso_hom_ι A' i)).trans
          ((Sigma.ι_map (fun i => g i) i).symm.trans
            ((congrArg (fun z => z ≫ Limits.Sigma.map g) (stalkSumIso_hom_ι A i)).symm.trans
              (Category.assoc _ _ _))))))

/-- The direct sum over the geometric fibre of the stalk functors of `X`, as a functor on
abelian sheaves on the small étale site of `X`. -/
private def fiberStalksCatFunctor (s : GeometricPoint Y.obj) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  Functor.pi' (fun x : GeometricFiberPoint B f s =>
    (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})) ⋙ Sigma.functor _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The direct sum over the geometric fibre of the stalk functors preserves all colimits: each
stalk functor does, and a coproduct of colimits is a colimit. -/
private theorem fiberStalksCatFunctor_preservesColimitsOfShape (s : GeometricPoint Y.obj)
    {J : Type w} [Category J] :
    PreservesColimitsOfShape J (fiberStalksCatFunctor.{u, v} B f s) := by
  have hpi : PreservesColimitsOfShape J (Functor.pi'
      (fun x : GeometricFiberPoint B f s =>
        (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v}))) := by
    have hcomp : PreservesColimitsOfShape J (Functor.pi'
        (fun x : GeometricFiberPoint B f s =>
          (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})) ⋙
        (piEquivalenceFunctorDiscrete (GeometricFiberPoint B f s)
          AddCommGrpCat.{max (u + 1) v}).functor) := by
      refine preservesColimitsOfShape_of_evaluation _ J fun x => ?_
      exact inferInstanceAs (PreservesColimitsOfShape J
        ((geometricPointSitePoint B X.obj X.property
          (x.as.toGeometricPoint B f s)).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})))
    exact preservesColimitsOfShape_of_reflects_of_preserves _
      (piEquivalenceFunctorDiscrete (GeometricFiberPoint B f s)
        AddCommGrpCat.{max (u + 1) v}).functor
  have hSigma : PreservesColimitsOfShape J
      (Sigma.functor (C := AddCommGrpCat.{max (u + 1) v}) (GeometricFiberPoint B f s)) := by
    rw [← piEquivalenceFunctorDiscrete_functor_comp_colim]
    infer_instance
  exact comp_preservesColimitsOfShape _ (Sigma.functor _)

/-- The composite of the direct image with compact support with a stalk functor of `Y` is the
direct sum over the geometric fibre of the stalk functors of `X`: this is the stalk decomposition,
read as an isomorphism of functors. -/
private def fShriekFiberNatIso (s : GeometricPoint Y.obj) :
    fShriekFunctor.{u, v} B f ⋙ (geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}) ≅
      fiberStalksCatFunctor.{u, v} B f s :=
  NatIso.ofComponents
    (fun F => fShriekStalkIso.{u, v} B f s F ≪≫ stalkSumIso
      (fun x : GeometricFiberPoint B f s =>
        AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)))
    (fun {F G} φ => by
      have hn := fShriekStalkIso_natural.{u, v} B f s φ
      have hs := stalkSumIso_natural
        (fun x : GeometricFiberPoint B f s =>
          AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj))
        (fun x : GeometricFiberPoint B f s =>
          AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) G.obj))
        (fun x => ((geometricPointSitePoint B X.obj X.property
          (x.toGeometricPoint B f s)).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map φ)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (stalkSumIso
            (fun x : GeometricFiberPoint B f s => AddCommGrpCat.of
              ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) G.obj))).hom) hn).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => (fShriekStalkIso.{u, v} B f s F).hom ≫ z) hs).trans
              (Category.assoc _ _ _).symm))))

/-- **The direct image with compact support preserves all colimits.** On stalks it is the direct
sum over the geometric fibre of the stalk functors, which preserves colimits, and the stalks at
the geometric points of `Y` jointly reflect colimits. -/
private theorem fShriekFunctor_preservesColimitsOfShape {J : Type w} [Category J]
    [HasColimitsOfShape J (Sheaf (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.{max (u + 1) v})]
    [HasColimitsOfShape J (Sheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{max (u + 1) v})] :
    PreservesColimitsOfShape J (fShriekFunctor.{u, v} B f) := by
  have hreflect := (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Y.obj
    Y.property).jointlyReflectsIsomorphisms
  have hcomp : ∀ s : GeometricPoint Y.obj, PreservesColimitsOfShape J
      (fShriekFunctor.{u, v} B f ⋙ (geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})) := by
    intro s
    have h1 : PreservesColimitsOfShape J (fiberStalksCatFunctor.{u, v} B f s) :=
      fiberStalksCatFunctor_preservesColimitsOfShape.{u, v, w} B f s
    exact preservesColimitsOfShape_of_natIso (fShriekFiberNatIso.{u, v} B f s).symm
  refine ⟨fun {K} => ?_⟩
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K) ?_
  refine hreflect.jointlyReflectsColimit fun s => ?_
  have := hcomp s
  exact isColimitOfPreserves (fShriekFunctor.{u, v} B f ⋙
    (geometricPointSitePoint B Y.obj Y.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})) (colimit.isColimit K)

/-- **Stacks 0F5F, part (2).** The direct image with compact support of a locally quasi-finite
morphism is an exact functor on abelian étale sheaves.

Preservation of finite colimits is the colimit preservation of the stalk decomposition;
preservation of finite limits follows from it together with preservation of monomorphisms. -/
@[stacks 0F5F "part (2), exactness"]
public theorem fShriekFunctor_exact :
    exactFunctor _ _ (fShriekFunctor.{u, v} B f) := by
  rw [exactFunctor_iff]
  have hcol : PreservesFiniteColimits (fShriekFunctor.{u, v} B f) :=
    ⟨fun _ _ _ => fShriekFunctor_preservesColimitsOfShape B f⟩
  have hbip : PreservesBinaryBiproducts (fShriekFunctor.{u, v} B f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : (fShriekFunctor.{u, v} B f).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have hmono : (fShriekFunctor.{u, v} B f).PreservesMonomorphisms :=
    fShriekFunctor_preservesMonomorphisms B f
  refine ⟨?_, inferInstance⟩
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (fShriekFunctor.{u, v} B f)).2 fun T hT => ?_
  have h1 : Mono T.f := hT.mono_f
  have h2 : Mono ((fShriekFunctor.{u, v} B f).map T.f) := inferInstance
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (fShriekFunctor.{u, v} B f)).1 hcol T hT).1, inferInstance⟩

/-- **Stacks 0F5F, part (2).** The direct image with compact support of a locally quasi-finite
morphism commutes with arbitrary direct sums of abelian étale sheaves. -/
@[stacks 0F5F "part (2), direct sums"]
public theorem fShriekFunctor_preservesCoproductsOfShape (I : Type (max (u + 1) v)) :
    PreservesColimitsOfShape (Discrete I) (fShriekFunctor.{u, v} B f) := by
  have h1 : HasColimitsOfShape (Discrete I)
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  have h2 : HasColimitsOfShape (Discrete I)
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  exact fShriekFunctor_preservesColimitsOfShape B f

end Exactness

end AlgebraicGeometry.SmallEtale

end
