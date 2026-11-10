module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor products of quasi-coherent modules on a site

The tensor product of two quasi-coherent sheaves of modules on a site with a sheaf of
commutative rings is quasi-coherent. This is the quasi-coherence assertion of **Stacks 0GQM**,
which is what makes the inclusion of the quasi-coherent modules into all modules a functor of
symmetric monoidal categories.

`StacksFrontier/CategoryTheory/Sites/Modules/TensorProduct/Basic.lean` proves the same statement on
a ringed *space*, where the covering argument is the intersection of two open covers. A site has
no intersections, so the two covers are refined here by the objects admitting a morphism into a
member of each: that family covers the final object by one application of transitivity, which is
the shape used for the same purpose by
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`.

The local input is the restriction isomorphism `tensorSheafificationOverIso`: the tensor product
of two sheaves of modules, restricted to the slice site over an object, is the tensor product
formed on that slice site.

## Main definitions

* `Stacks.SheafOfModules.TensorProduct.overStructurePresheaf`: the presheaf of commutative rings
  of the slice site over an object, obtained by restricting along `CategoryTheory.Over.forget`.
* `Stacks.SheafOfModules.TensorProduct.presheafModuleOverRestriction`: restriction of a presheaf
  of modules to the slice site over an object.
* `Stacks.SheafOfModules.TensorProduct.tensorPresheafOverRestrictionIso` and
  `Stacks.SheafOfModules.TensorProduct.tensorSheafOverRestrictionValIso`: the two pointwise
  comparisons out of which the restriction map on tensor products is built.
* `Stacks.SheafOfModules.TensorProduct.tensorSheafificationOverIso`: the restriction to the slice
  site over an object of a tensor product of sheaves of modules is the tensor product formed on
  that slice site.

## Main results

* `Stacks.SheafOfModules.TensorProduct.isSheaf_overStructurePresheaf`: the restriction of a sheaf
  of commutative rings to a slice site is a sheaf.
* `Stacks.SheafOfModules.TensorProduct.structureSheaf_over_eq`: that restricted sheaf of rings is
  the sheaf of rings of the slice, on the nose.
* `Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf'`: **Stacks 0GQM** — the
  tensor product of two quasi-coherent sheaves of modules on a site is quasi-coherent. The
  unprimed name is this statement for the structure sheaf of a fixed sheaf of rings on a stack
  site, registered there as an instance.

## Implementation notes

Quasi-coherence is Mathlib's `SheafOfModules.IsQuasicoherent`, the predicate of Stacks 03DL(6)
that asks for a family covering the final object on whose members the module has a presentation
by free modules. It is the predicate carried by `AlgebraicGeometry.Stack.QuasiCoherentModule` and
by the ringed-space tensor-product instance, so the result here is directly usable by both. The
sheafification-free variant `SheafOfModules.IsQuasicoherentOnSite` expresses the same condition
one object at a time; no comparison between the two is made here.

`tensorSheafificationOverIso` follows the route of the ringed-space file: the two presheaves of
modules being compared are identified *pointwise* rather than as whole structures — over an
object of the slice both are literally the same tensor product of modules — and the comparison
map of sheaves is obtained from the sheafification adjunction. That it is an isomorphism is in
`CategoryTheory.GrothendieckTopology.W`, the morphisms of presheaves that sheafification inverts:
the middle map is the restriction of a sheafification unit, hence locally bijective by
`CategoryTheory.Presheaf.isLocallyInjective_whisker` and its surjective counterpart, the outer two
are isomorphisms, and `W` is multiplicative with the two-out-of-three property, which is what
turns `W` of the composite into `W` of the comparison map.

`Stacks.TensorCoherence.tensorSheafOverIso` is the same statement for a different spelling of the
tensor product of sheaves of modules, `Stacks.sheafTensorRight`, and the implementation notes of
that file explain why the three spellings on this branch are not compared to each other. The
spelling needed here is forced: the presentation machinery this file consumes —
`Stacks.SheafOfModules.TensorProduct.tensorPresentation`,
`Stacks.SheafOfModules.TensorProduct.freeTensorIso` and
`Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite` — is stated for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, so the restriction isomorphism is needed
for that one.

The hypotheses are the ones the inputs need and no others. Sheafification of abelian-group-valued
presheaves is required on the site and on each of its slices, because a presentation of the
restriction of a module to a slice is a statement about that slice; this is the hypothesis shape
of `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`. Fibre products in the site are
needed for a single step, `SheafOfModules.overMap` being a left adjoint, which is what carries a
presentation along a morphism of the site; the sites of Stacks 0GQM — the fppf site of an
algebraic stack and the small sites of a scheme — have them.

## References

* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open Stacks.SheafOfModules.TensorPresentations
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafOfModules.TensorProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (V : C)

/-- The presheaf of commutative rings of the slice site over `V`: the structure presheaf
restricted along `CategoryTheory.Over.forget V`. -/
@[sga "3 IV 4.3.17" "special case"]
abbrev overStructurePresheaf : (CategoryTheory.Over V)ᵒᵖ ⥤ CommRingCat.{w} :=
  (CategoryTheory.Over.forget V).op ⋙ 𝒪

/-- The restriction of a sheaf of commutative rings to the slice site over `V` is a sheaf: it is
the pullback of the sheaf along the continuous functor `CategoryTheory.Over.forget V`. -/
theorem isSheaf_overStructurePresheaf (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪)) :
    Presheaf.IsSheaf (J.over V) (structureRingPresheaf (overStructurePresheaf 𝒪 V)) :=
  ((structureSheaf 𝒪 h𝒪).over V).property

/-- The sheaf of rings of the slice site over `V` *is* the restriction of the sheaf of rings of
the site: the two are equal, not merely isomorphic, so a sheaf of modules on the slice over the
one is a sheaf of modules over the other with no transport. -/
theorem structureSheaf_over_eq (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪)) :
    (structureSheaf 𝒪 h𝒪).over V = structureSheaf (overStructurePresheaf 𝒪 V)
      (isSheaf_overStructurePresheaf 𝒪 V h𝒪) := rfl

/-- Restriction of a presheaf of modules to the slice site over `V`: the pushforward of presheaves
of modules along `CategoryTheory.Over.forget V`.

The functor being pushed forward along is given explicitly, which is what makes the two pointwise
comparisons below statable: written inline it is a metavariable that only a type ascription on the
resulting morphism could fix, and that ascription would identify the two presheaves of modules as
whole structures. -/
@[sga "3 I 3.1.4", sga "3 IV 4.3.17" "special case"]
noncomputable def presheafModuleOverRestriction :
    PresheafOfModules.{w} (structureRingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (structureRingPresheaf (overStructurePresheaf 𝒪 V)) :=
  PresheafOfModules.pushforward (F := CategoryTheory.Over.forget V)
    (𝟙 (structureRingPresheaf (overStructurePresheaf 𝒪 V)))

section Restriction

variable (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over V).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over V) AddCommGrpCat.{w}]

/-- The presheaf tensor product on the slice site over `V` of the restrictions of `F` and `G` is
the restriction of their presheaf tensor product. Over each object of the slice both sides are
literally the same tensor product of modules, so the identification is made pointwise. -/
noncomputable def tensorPresheafOverRestrictionIso
    (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (PresheafOfModules.tensorObj (O := (overStructurePresheaf 𝒪 V)) ((F.over V).val)
        ((G.over V).val)) ≅
      (presheafModuleOverRestriction 𝒪 V).obj
        ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val))) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The restriction to the slice site over `V` of the underlying presheaf of modules of
`F ⊗_𝒪 G` is the underlying presheaf of modules of the restriction of `F ⊗_𝒪 G`. Pointwise for
the same reason as `Stacks.SheafOfModules.TensorProduct.tensorPresheafOverRestrictionIso`. -/
noncomputable def tensorSheafOverRestrictionValIso
    (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (presheafModuleOverRestriction 𝒪 V).obj
        ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
                (h𝒪)⟩).obj (F)).obj (G)))) ≅
      (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
            (h𝒪)⟩).obj (F)).obj (G))).over V).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- **Tensor products commute with restriction to a slice site.** The restriction to the slice
site over `V` of the tensor product of two sheaves of modules is the tensor product, formed on
that slice site, of their restrictions.

The comparison map is the restriction of the sheafification unit of the presheaf tensor product,
pre- and post-composed with the two pointwise identifications, transposed across the
sheafification adjunction. It is an isomorphism because all three factors lie in
`CategoryTheory.GrothendieckTopology.W`: the middle one is the restriction of a sheafification
unit, hence locally bijective, and the outer two are isomorphisms. -/
noncomputable def tensorSheafificationOverIso
    (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
          (h𝒪)⟩).obj (F)).obj (G))).over V ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(overStructurePresheaf 𝒪 V), Presheaf.isSheaf_of_isSheaf_comp _
          ((overStructurePresheaf 𝒪 V)) (forget₂ CommRingCat RingCat)
          ((isSheaf_overStructurePresheaf 𝒪 V h𝒪))⟩).obj ((F.over V))).obj ((G.over V))) := by
  let JV := J.over V
  let 𝒪V := overStructurePresheaf 𝒪 V
  let h𝒪V := isSheaf_overStructurePresheaf 𝒪 V h𝒪
  let T := (PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val))
  let P : PresheafOfModules.{w} (structureRingPresheaf 𝒪V) :=
    (PresheafOfModules.tensorObj (O := 𝒪V) ((F.over V).val) ((G.over V).val))
  let M := ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
        (h𝒪)⟩).obj (F)).obj (G))).over V
  let mid := (presheafModuleOverRestriction 𝒪 V).map (toSheafify 𝒪 h𝒪 T)
  let γ : P ⟶ M.val := (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G).hom ≫ mid ≫
    (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G).hom
  let adj := sheafifyAdjunction 𝒪V h𝒪V
  let η := toSheafify 𝒪V h𝒪V P
  let e : (sheafify 𝒪V h𝒪V).obj P ⟶ M := (adj.homEquiv P M).symm γ
  let forgetMap := (SheafOfModules.forget (structureSheaf 𝒪V h𝒪V) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪V h𝒪V).obj))
  have hecomp : η ≫ forgetMap.map e = γ :=
    (adj.homEquiv_unit (f := e)).symm.trans ((adj.homEquiv P M).apply_symm_apply γ)
  let toAbV := PresheafOfModules.toPresheaf (structureSheaf 𝒪V h𝒪V).obj
  -- `Functor.mapIso` in term position rather than `inferInstance`: searching for
  -- `IsIso (toAbV.map _)` has to unify against `Iso.hom ?e`, which needs `Functor.mapIso`
  -- unfolded, and instance search works at reducible transparency only.
  have hIsoSrc : IsIso (toAbV.map (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G).hom) :=
    (toAbV.mapIso (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G)).isIso_hom
  have hIsoTgt : IsIso (toAbV.map (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G).hom) :=
    (toAbV.mapIso (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G)).isIso_hom
  have hmidI : Presheaf.IsLocallyInjective JV (toAbV.map mid) := by
    change Presheaf.IsLocallyInjective JV (Functor.whiskerLeft
      (CategoryTheory.Over.forget V).op
      ((PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj).map (toSheafify 𝒪 h𝒪 T)))
    have : Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj).map (toSheafify 𝒪 h𝒪 T)) := by
      change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J T.presheaf)
      infer_instance
    exact Presheaf.isLocallyInjective_whisker JV J (CategoryTheory.Over.forget V) _
  have hmidS : Presheaf.IsLocallySurjective JV (toAbV.map mid) := by
    change Presheaf.IsLocallySurjective JV (Functor.whiskerLeft
      (CategoryTheory.Over.forget V).op
      ((PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj).map (toSheafify 𝒪 h𝒪 T)))
    have : Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj).map (toSheafify 𝒪 h𝒪 T)) := by
      change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J T.presheaf)
      infer_instance
    exact Presheaf.isLocallySurjective_whisker JV J (CategoryTheory.Over.forget V) _
  -- Term mode with an explicitly applied `congrArg`: `rw [Functor.map_comp]` reports the
  -- pattern as absent here, the two `Category` instances on the index presheaf being reached
  -- by different routes.
  have hsplit : toAbV.map γ =
      toAbV.map (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G).hom ≫ toAbV.map mid ≫
        toAbV.map (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G).hom :=
    (toAbV.map_comp _ _).trans
      (congrArg (fun z => toAbV.map (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G).hom ≫ z)
        (toAbV.map_comp mid (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G).hom))
  have hmidW : JV.W (toAbV.map mid) :=
    (JV.W_iff_isLocallyBijective (toAbV.map mid)).2 ⟨hmidI, hmidS⟩
  have hηW : JV.W (toAbV.map η) := JV.W_toSheafify P.presheaf
  -- The two isomorphisms are fed to `ObjectProperty.isLocal_of_isIso` through a `have` of their
  -- own: two anonymous `have`s of `IsIso` in one tactic block leave only the last one visible to
  -- instance search, so the second application fails to find its hypothesis.
  have hWsrc : JV.W (toAbV.map (tensorPresheafOverRestrictionIso 𝒪 V h𝒪 F G).hom) :=
    have := hIsoSrc
    ObjectProperty.isLocal_of_isIso _ _
  have hWtgt : JV.W (toAbV.map (tensorSheafOverRestrictionValIso 𝒪 V h𝒪 F G).hom) :=
    have := hIsoTgt
    ObjectProperty.isLocal_of_isIso _ _
  have hγW : JV.W (toAbV.map γ) := by
    rw [hsplit]
    exact JV.W.comp_mem _ _ hWsrc (JV.W.comp_mem _ _ hmidW hWtgt)
  have hcompAb : toAbV.map η ≫ toAbV.map e.val = toAbV.map γ :=
    (toAbV.map_comp η (forgetMap.map e)).symm.trans (congrArg toAbV.map hecomp)
  -- `cast` rather than `rw [hcompAb]`: the composite in the goal and the one in `hcompAb` are
  -- the same term up to the route by which the functor category instance is reached, which
  -- `rw` reports as a missing pattern.
  have heW : JV.W (toAbV.map e.val) :=
    JV.W.of_precomp (W' := JV.W) (toAbV.map η) (toAbV.map e.val) hηW
      (cast (congrArg (fun k => JV.W k) hcompAb).symm hγW)
  have heIso : IsIso e :=
    (isIso_iff_of_reflects_iso e (SheafOfModules.toSheaf (structureSheaf 𝒪V h𝒪V))).mp
      ((JV.W_sheafToPresheaf_map_iff_isIso _).1 heW)
  exact (asIso e).symm

end Restriction

section Quasicoherent

variable (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [UnivLE.{max v u, w}] [HasPullbacks C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]

omit [UnivLE.{max v u, w}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Stacks 0GQM.** The tensor product of two quasi-coherent sheaves of modules on a site is
quasi-coherent.

Each factor is presented on some family covering the final object. The two families are refined
by the objects carrying a morphism into a member of each, which again covers the final object:
given an object, the first family covers it, each member of that cover is covered by the second
family, and every object of the resulting cover maps to a member of both. On such an object the
two presentations restrict, their tensor product presents the tensor product of the restrictions
by `Stacks.SheafOfModules.TensorProduct.tensorPresentation`, and that is the restriction of
`F ⊗_𝒪 G` by `Stacks.SheafOfModules.TensorProduct.tensorSheafificationOverIso`. -/
@[stacks 0GQM "tensor products of quasi-coherent modules are quasi-coherent",
  ega "I 9.1.1" "more general"]
theorem isQuasicoherent_tensorSheaf'
    (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
          (h𝒪)⟩).obj (F)).obj (G))).IsQuasicoherent := by
  classical
  let R := structureSheaf 𝒪 h𝒪
  let qF : SheafOfModules.QuasicoherentData.{u} F :=
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)).some
  let qG : SheafOfModules.QuasicoherentData.{u} G :=
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)).some
  have hT : J.CoversTop
      (fun t : Σ W : C, (Σ i : qF.I, W ⟶ qF.X i) × (Σ j : qG.I, W ⟶ qG.X j) => t.1) := by
    intro Y
    refine J.transitive (qF.coversTop Y) _ ?_
    intro Z g hg
    obtain ⟨i, ⟨α⟩⟩ := (Sieve.mem_ofObjects_iff qF.X g).mp hg
    refine J.superset_covering ?_ (qG.coversTop Z)
    intro W b hb
    obtain ⟨j, ⟨β⟩⟩ := (Sieve.mem_ofObjects_iff qG.X b).mp hb
    exact ⟨⟨W, ⟨i, b ≫ α⟩, ⟨j, β⟩⟩, ⟨𝟙 W⟩⟩
  refine SheafOfModules.QuasicoherentData.isQuasicoherent
    { I := Σ W : C, (Σ i : qF.I, W ⟶ qF.X i) × (Σ j : qG.I, W ⟶ qG.X j)
      X := fun t => t.1
      coversTop := hT
      presentation := fun t => ?_ }
  obtain ⟨W, ⟨i, a⟩, ⟨j, b⟩⟩ := t
  -- Restrict a presentation of `M.over X` along `a : W ⟶ X` to one of `M.over W`.
  let restrict {M : SheafOfModules R} {X : C} (a : W ⟶ X) (p : (M.over X).Presentation) :
      (M.over W).Presentation :=
    have : PreservesColimitsOfSize.{w, w} (SheafOfModules.overMap (R := R) a) := inferInstance
    ((p.map (SheafOfModules.overMap (R := R) a) (SheafOfModules.overMapUnitIso (R := R) a)).ofIsIso
      ((SheafOfModules.overFunctorMap (R := R) a).app M).hom)
  let pF := restrict a (qF.presentation i)
  let pG := restrict b (qG.presentation j)
  let e := tensorSheafificationOverIso 𝒪 W h𝒪 F G
  have : IsIso e.symm.hom := e.symm.isIso_hom
  exact (tensorPresentation (overStructurePresheaf 𝒪 W) (isSheaf_overStructurePresheaf 𝒪 W h𝒪)
    pF pG).ofIsIso e.symm.hom

end Quasicoherent

end Stacks.SheafOfModules.TensorProduct

end
