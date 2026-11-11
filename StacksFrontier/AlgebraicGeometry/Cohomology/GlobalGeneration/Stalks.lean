module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Generation by global sections, tested on stalks

Let `O_X` be a sheaf of rings on a topological space `X` and let `F` be a sheaf of
`O_X`-modules. A family `s : I → F.sections` of global sections of `F` determines a morphism
`F.freeHomEquiv.symm s` from the free sheaf of modules on `I`, and the family generates `F`
exactly when that morphism is an epimorphism. This module characterizes that condition
pointwise: it holds if and only if, at every point of `X`, the germs of the `s i` span the
stalk of `F` as a module over the stalk of `O_X`.

## Main results

* `AlgebraicGeometry.generates_iff_stalkwise_generates`: a family of global sections generates a
  sheaf of modules if and only if its germs span every stalk.

## Implementation notes

The argument factors through two steps. First, a morphism of sheaves of modules is an
epimorphism exactly when it is surjective on every stalk, because the stalk functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor` preserves colimits and a section of a sheaf is
determined by its germs. Second, the stalk of the free sheaf on `I` is identified with the
finitely supported functions `I →₀ O_{X,x}`, in such a way that the basis vector at `i` goes to
the germ of `s i`; surjectivity of the induced map then becomes the statement that the germs
span.

That second identification is assembled from the stalk of a single copy of the structure sheaf
(`LocallyFreeRank.unitStalkLEquiv`) together with the fact that the stalk functor turns the
coproduct presentation of the free sheaf into a direct sum of modules.

## References

* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits

universe u

namespace AlgebraicGeometry

/-- The stalk at `x` of the free sheaf of `O`-modules on `I`, presented as the coproduct of `I`
copies of the stalk of the structure sheaf. -/
public noncomputable def freeStalkCoproductIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) (I : Type u) :
    (∐ fun _ : I => (SheafOfModules.stalkFunctor O x).obj (SheafOfModules.unit O)) ≅
      (SheafOfModules.stalkFunctor O x).obj (SheafOfModules.free I) := by
  classical
  let F := SheafOfModules.stalkFunctor O x
  let Z : I → ModuleCat (TopCat.Presheaf.stalk O.obj x : RingCat) :=
    fun _ => F.obj (SheafOfModules.unit O)
  let c := SheafOfModules.freeCofan (R := O) I
  have hc0 : IsColimit (F.mapCocone c) :=
    isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I)
  have hc : IsColimit (Cofan.mk (F.obj (SheafOfModules.free I))
      (fun i => F.map (c.inj i)) : Cofan Z) :=
    (Cofan.isColimitMapCoconeEquiv F _ c) hc0
  exact (coproductIsCoproduct Z).coconePointUniqueUpToIso hc

/-- `AlgebraicGeometry.freeStalkCoproductIso` is compatible with the coproduct inclusions: the
`i`-th inclusion corresponds to the stalk of the `i`-th inclusion of the free sheaf. -/
private theorem freeStalkCoproductIso_ι {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) (I : Type u) (i : I) :
    Sigma.ι (fun _ : I =>
      (SheafOfModules.stalkFunctor O x).obj (SheafOfModules.unit O)) i ≫
        (freeStalkCoproductIso O x I).hom =
      (SheafOfModules.stalkFunctor O x).map (SheafOfModules.ιFree i) := by
  classical
  unfold freeStalkCoproductIso
  exact (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom _ (Discrete.mk i)

/-- The stalk at `x` of the structure sheaf regarded as a module over itself is the stalk ring
`O_{X,x}` as a module over itself. -/
public noncomputable def stalkUnitLinearEquiv {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    ((SheafOfModules.stalkFunctor O x).obj (SheafOfModules.unit O) : Type u) ≃ₗ[
      ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u)]
      ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u) :=
  LocallyFreeRank.unitStalkLEquiv O.obj x

/-- `AlgebraicGeometry.stalkUnitLinearEquiv` takes the germ of the unit section to `1`. -/
private theorem stalkUnitLinearEquiv_germ_one {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    stalkUnitLinearEquiv O x
      ((TopCat.Presheaf.germ (SheafOfModules.unit O).val.presheaf ⊤ x (Set.mem_univ x)).hom
        (1 : ((O.obj.obj (Opposite.op ⊤) : RingCat) : Type u))) = 1 := by
  let F := forget₂ RingCat.{u} AddCommGrpCat.{u}
  let D := (OpenNhds.inclusion x).op ⋙ O.obj
  let pIso := preservesColimitIso F D
  have hpIso : pIso = preservesColimitIso F D := rfl
  let addE := pIso.symm.addCommGroupIsoToAddEquiv
  have h := ι_preservesColimitIso_inv F D (Opposite.op ⟨⊤, Set.mem_univ x⟩)
  rw [← hpIso] at h
  have h' := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f)
      (1 : ((O.obj.obj (Opposite.op ⊤) : RingCat) : Type u))) h
  change addE
      ((TopCat.Presheaf.germ (SheafOfModules.unit O).val.presheaf ⊤ x (Set.mem_univ x)).hom
        (1 : ((O.obj.obj (Opposite.op ⊤) : RingCat) : Type u))) =
    (1 : ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u))
  calc
    _ = (TopCat.Presheaf.germ O.obj ⊤ x (Set.mem_univ x)).hom 1 := h'
    _ = 1 := by simp

/-- The stalk at `x` of the free sheaf of `O`-modules on `I` is the module of finitely supported
functions `I →₀ O_{X,x}`. -/
public noncomputable def freeStalkLinearEquiv {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) (I : Type u) :
    ((SheafOfModules.stalkFunctor O x).obj (SheafOfModules.free I) : Type u) ≃ₗ[
      ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u)]
      (I →₀ ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u)) := by
  classical
  exact (freeStalkCoproductIso O x I).symm.toLinearEquiv.trans
    ((ModuleCat.coprodIsoDirectSum (fun _ : I =>
        (SheafOfModules.stalkFunctor O x).obj (SheafOfModules.unit O))).toLinearEquiv.trans
      ((DirectSum.congrLinearEquiv (fun _ : I => stalkUnitLinearEquiv O x)).trans
        (finsuppLEquivDirectSum
          (TopCat.Presheaf.stalk O.obj x : RingCat)
          (TopCat.Presheaf.stalk O.obj x : RingCat) I).symm))

/-- Under `AlgebraicGeometry.freeStalkLinearEquiv`, the basis vector supported at `i` corresponds
to the germ of the `i`-th inclusion applied to the unit of the stalk ring. -/
private theorem freeStalkLinearEquiv_symm_single {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) (I : Type u) (i : I) :
    (freeStalkLinearEquiv O x I).symm (Finsupp.single i 1) =
      (SheafOfModules.stalkFunctor O x).map (SheafOfModules.ιFree i)
        ((stalkUnitLinearEquiv O x).symm 1) := by
  classical
  let F := SheafOfModules.stalkFunctor O x
  let Z : I → ModuleCat (TopCat.Presheaf.stalk O.obj x : RingCat) :=
    fun _ => F.obj (SheafOfModules.unit O)
  have hι' (a : Z i) :
      (freeStalkCoproductIso O x I).symm.hom (F.map (SheafOfModules.ιFree i) a) =
        Sigma.ι Z i a := by
    have h := congrArg (fun f => f a) (freeStalkCoproductIso_ι O x I i)
    change (freeStalkCoproductIso O x I).hom (Sigma.ι Z i a) =
      F.map (SheafOfModules.ιFree i) a at h
    rw [Iso.symm_hom, ← h, Iso.hom_inv_id_apply]
  apply (freeStalkLinearEquiv O x I).injective
  simp only [LinearEquiv.apply_symm_apply]
  unfold freeStalkLinearEquiv
  simp only [LinearEquiv.trans_apply, CategoryTheory.Iso.toLinearEquiv_apply]
  change Finsupp.single i 1 =
    (finsuppLEquivDirectSum
      (TopCat.Presheaf.stalk O.obj x : RingCat)
      (TopCat.Presheaf.stalk O.obj x : RingCat) I).symm
      ((DirectSum.congrLinearEquiv (fun _ : I => stalkUnitLinearEquiv O x))
        ((ModuleCat.coprodIsoDirectSum Z).hom
          ((freeStalkCoproductIso O x I).symm.hom
            (F.map (SheafOfModules.ιFree i) ((stalkUnitLinearEquiv O x).symm 1)))))
  rw [hι' ((stalkUnitLinearEquiv O x).symm 1)]
  have hcop (b : Z i) : (ModuleCat.coprodIsoDirectSum Z).hom (Sigma.ι Z i b) =
      DirectSum.lof (TopCat.Presheaf.stalk O.obj x : RingCat) I
        (fun _ : I => (Z i : Type u)) i b :=
    (congrArg (fun f => f b) (ModuleCat.ι_coprodIsoDirectSum_hom Z i) :)
  rw [hcop ((stalkUnitLinearEquiv O x).symm 1)]
  change Finsupp.single i 1 =
    (finsuppLEquivDirectSum
      (TopCat.Presheaf.stalk O.obj x : RingCat)
      (TopCat.Presheaf.stalk O.obj x : RingCat) I).symm
      ((DirectSum.congrLinearEquiv (fun _ : I => stalkUnitLinearEquiv O x)).toLinearMap
        (DirectSum.lof (TopCat.Presheaf.stalk O.obj x : RingCat) I
          (fun _ : I => (Z i : Type u)) i ((stalkUnitLinearEquiv O x).symm 1)))
  rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]
  simp [finsuppLEquivDirectSum_symm_lof]

variable {X : TopCat.{u}} (O_X : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (F : SheafOfModules.{u} O_X) {I : Type u}

/-- A morphism of sheaves of modules is an epimorphism if and only if it is surjective on every
stalk. -/
public theorem epi_iff_stalk_surjective {M N : SheafOfModules.{u} O_X} (f : M ⟶ N) :
    Epi f ↔ ∀ x : X, Function.Surjective
      (((SheafOfModules.stalkFunctor O_X x).map f).hom) := by
  constructor
  · intro _ x
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  · intro h
    refine ⟨fun {Z} g k hgk => ?_⟩
    apply SheafOfModules.hom_ext
    ext U s
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf O_X).obj Z) U.unop
    intro x hx
    let G := SheafOfModules.stalkFunctor O_X x
    let m := (TopCat.Presheaf.germ N.val.presheaf U.unop x hx).hom s
    obtain ⟨t, ht⟩ := h x m
    have hpoint : (G.map g).hom ((G.map f).hom t) =
        (G.map k).hom ((G.map f).hom t) := by
      simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
        congrArg (fun q => q.hom t) (congrArg G.map hgk)
    have hgerm (q : N ⟶ Z) :
        (G.map q).hom m =
          (TopCat.Presheaf.germ Z.val.presheaf U.unop x hx).hom
            (q.val.app (Opposite.op U.unop) s) := by
      change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf O_X.obj).map q.val) _ = _
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hx
        ((PresheafOfModules.toPresheaf O_X.obj).map q.val) s
    change (TopCat.Presheaf.germ Z.val.presheaf U.unop x hx).hom
        (g.val.app U s) =
      (TopCat.Presheaf.germ Z.val.presheaf U.unop x hx).hom (k.val.app U s)
    rw [← hgerm g, ← hgerm k, ← ht]
    exact hpoint

/-- The morphism from the free sheaf determined by `s` sends the basis vector at `i` in the stalk
to the germ of the global section `s i`. -/
private theorem freeHom_stalk_single_germ (s : I → F.sections) (x : X) (i : I) :
    (((SheafOfModules.stalkFunctor O_X x).map (F.freeHomEquiv.symm s)).hom)
        ((freeStalkLinearEquiv O_X x I).symm (Finsupp.single i 1)) =
      (TopCat.Presheaf.germ F.val.presheaf ⊤ x (Set.mem_univ x)).hom
        ((s i).eval (Opposite.op ⊤)) := by
  let G := SheafOfModules.stalkFunctor O_X x
  let f := F.freeHomEquiv.symm s
  rw [freeStalkLinearEquiv_symm_single]
  have hunit : (stalkUnitLinearEquiv O_X x).symm 1 =
      (TopCat.Presheaf.germ (SheafOfModules.unit O_X).val.presheaf ⊤ x (Set.mem_univ x)).hom
        (1 : ((O_X.obj.obj (Opposite.op ⊤) : RingCat) : Type u)) :=
    (LinearEquiv.symm_apply_eq _).mpr (stalkUnitLinearEquiv_germ_one O_X x).symm
  have hsection : F.unitHomEquiv (SheafOfModules.ιFree i ≫ f) = s i := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp [f]
  have hvalue := SheafOfModules.unitHomEquiv_apply_coe F
    (SheafOfModules.ιFree i ≫ f) (Opposite.op ⊤)
  rw [hsection] at hvalue
  have hcomp_apply : (G.map (SheafOfModules.ιFree i ≫ f)).hom
      ((stalkUnitLinearEquiv O_X x).symm 1) =
      (G.map f).hom
      ((G.map (SheafOfModules.ιFree i)).hom ((stalkUnitLinearEquiv O_X x).symm 1)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun q => q.hom ((stalkUnitLinearEquiv O_X x).symm 1))
        (G.map_comp (SheafOfModules.ιFree i) f)
  rw [← hcomp_apply, hunit]
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf O_X.obj).map
        (SheafOfModules.ιFree i ≫ f).val)
      ((TopCat.Presheaf.germ (SheafOfModules.unit O_X).val.presheaf ⊤ x
          (Set.mem_univ x)).hom
        (show ((SheafOfModules.unit O_X).val.obj (Opposite.op ⊤) : Type u) from
          (1 : ((O_X.obj.obj (Opposite.op ⊤) : RingCat) : Type u)))) = _
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat) (U := ⊤) (x := x) (hx := Set.mem_univ x)
    ((PresheafOfModules.toPresheaf O_X.obj).map
      (SheafOfModules.ιFree i ≫ f).val)
    (1 : ((O_X.obj.obj (Opposite.op ⊤) : RingCat) : Type u))
  refine hmap.trans ?_
  simp only [hvalue, PresheafOfModules.toPresheaf]
  rfl

/-- The image of the map on stalks induced by the morphism from the free sheaf is the span of the
germs of the global sections `s i`. -/
public theorem freeHom_stalk_range (s : I → F.sections) (x : X) :
    LinearMap.range
        (((SheafOfModules.stalkFunctor O_X x).map
          (F.freeHomEquiv.symm s)).hom.comp
          (freeStalkLinearEquiv O_X x I).symm.toLinearMap) =
      Submodule.span (R := (TopCat.Presheaf.stalk O_X.obj x : RingCat))
        (Set.range fun i ↦
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x (Set.mem_univ x)).hom
            ((s i).eval (Opposite.op ⊤))) := by
  classical
  let G := SheafOfModules.stalkFunctor O_X x
  let e := freeStalkLinearEquiv O_X x I
  let q : (I →₀ ((TopCat.Presheaf.stalk O_X.obj x : RingCat) : Type u)) →ₗ[
      (TopCat.Presheaf.stalk O_X.obj x : RingCat)] (G.obj F : Type u) :=
    (G.map (F.freeHomEquiv.symm s)).hom.comp e.symm.toLinearMap
  have hq_single (i : I) : q (Finsupp.single i 1) =
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x (Set.mem_univ x)).hom
        ((s i).eval (Opposite.op ⊤)) := freeHom_stalk_single_germ O_X F s x i
  change q.range = Submodule.span
    (R := (TopCat.Presheaf.stalk O_X.obj x : RingCat)) (Set.range fun i ↦
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x (Set.mem_univ x)).hom
      ((s i).eval (Opposite.op ⊤)))
  rw [LinearMap.range_eq_map, ← Finsupp.supported_univ,
    Finsupp.supported_eq_span_single, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hq_single i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, hq_single i⟩

/-- Surjectivity on the stalk at `x` of the morphism from the free sheaf determined by `s` is the
same as the germs of the `s i` spanning the stalk of `F` at `x`. -/
public theorem freeHom_stalk_surjective_iff_span (s : I → F.sections) (x : X) :
    Function.Surjective
        (((SheafOfModules.stalkFunctor O_X x).map
          (F.freeHomEquiv.symm s)).hom) ↔
      Submodule.span (R := (TopCat.Presheaf.stalk O_X.obj x : RingCat))
        (Set.range fun i ↦
          (TopCat.Presheaf.germ F.val.presheaf ⊤ x (by trivial)).hom
            ((s i).eval (Opposite.op ⊤))) = ⊤ := by
  classical
  let G := SheafOfModules.stalkFunctor O_X x
  let e := freeStalkLinearEquiv O_X x I
  let q : (I →₀ ((TopCat.Presheaf.stalk O_X.obj x : RingCat) : Type u)) →ₗ[
      (TopCat.Presheaf.stalk O_X.obj x : RingCat)] (G.obj F : Type u) :=
    (G.map (F.freeHomEquiv.symm s)).hom.comp e.symm.toLinearMap
  rw [← LinearMap.range_eq_top, ← LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (freeStalkLinearEquiv O_X x I).symm), freeHom_stalk_range]
  rfl

/-- **Global sections generate a sheaf of modules iff their germs generate every stalk.** Let
`O_X` be a sheaf of rings on a topological space `X`, `F` a sheaf of `O_X`-modules and
`s : I → Γ(X, F)` a family of global sections. The sections generate `F`, that is, the morphism
`⨁_{i ∈ I} O_X ⟶ F` they determine (`F.freeHomEquiv.symm s`) is an epimorphism of sheaves of
`O_X`-modules, if and only if for every `x : X` the germs `s_{i,x}` span the stalk `F_x` as a
module over `O_{X,x}`. -/
@[stacks 01AN]
public theorem generates_iff_stalkwise_generates (s : I → F.sections) :
    Epi (F.freeHomEquiv.symm s) ↔
      ∀ x : X,
        Submodule.span (R := (TopCat.Presheaf.stalk O_X.obj x : RingCat))
          (Set.range fun i ↦
            (TopCat.Presheaf.Γgerm F.val.presheaf x).hom
              ((s i).eval (Opposite.op ⊤))) = ⊤ := by
  rw [epi_iff_stalk_surjective]
  exact forall_congr' fun x => freeHom_stalk_surjective_iff_span O_X F s x

/-- **The germs of a trivializing family of global sections form a basis of every stalk.** If the
morphism `F.freeHomEquiv.symm s` from the free sheaf of modules on `I` determined by a family
`s : I → F.sections` is an isomorphism, then at every point `x` the germs of the `s i` are an
`O_{X,x}`-basis of the stalk `F_x`.

This is the converse direction to `Stacks.SheafOfModules.exists_sections_germ_eq`, and the
statement pins the basis down completely: a `Module.Basis` is determined by the family of its
members, which the second component names, so nothing is discarded by the existential.

The proof is the composite of `AlgebraicGeometry.freeStalkLinearEquiv` — the identification of
the stalk of the free sheaf with `I →₀ O_{X,x}` — with the stalk of the given isomorphism, and
`AlgebraicGeometry.freeHom_stalk_single_germ` identifies where the basis vectors go. Both of
those are `private` to this module, which is why this accessor lives here rather than with its
consumers. -/
public theorem exists_stalkBasis_of_isIso_freeHom (s : I → F.sections)
    [IsIso (F.freeHomEquiv.symm s)] (x : X) :
    ∃ b : Module.Basis I ((TopCat.Presheaf.stalk O_X.obj x : RingCat) : Type u)
        ((SheafOfModules.stalkFunctor O_X x).obj F : Type u),
      ∀ i : I, b i = (TopCat.Presheaf.Γgerm F.val.presheaf x).hom ((s i).eval (Opposite.op ⊤)) := by
  classical
  refine ⟨Finsupp.basisSingleOne.map ((freeStalkLinearEquiv O_X x I).symm.trans
    (asIso ((SheafOfModules.stalkFunctor O_X x).map (F.freeHomEquiv.symm s))).toLinearEquiv),
    fun i => ?_⟩
  rw [Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  exact freeHom_stalk_single_germ O_X F s x i

end AlgebraicGeometry
