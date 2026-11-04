module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageReduction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush
public import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of the direct image of modules along a closed immersion of ringed topoi

Let `i : (Sh(C), O) → (Sh(D), O')` be a morphism of ringed topoi which is a closed immersion of
topoi and whose structure map `i^# : O' ⟶ i_*O` is surjective, and let `I ⊆ O'` be the sectionwise
kernel of `i^#`. [Stacks, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
asserts, among other things, that the essential image of `i_* : Mod(O) ⥤ Mod(O')` consists exactly
of the `O'`-modules `G` annihilated by `I`. This file proves that biconditional.

The direct image factors as
`Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor i O` followed by restriction of scalars
along `i^#`. Two of the three ingredients are already on this branch:

* restriction of scalars along a locally surjective `i^#` has the `I`-annihilated modules as its
  essential image
  (`Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_iff`, Stacks' inlined step
  "`i_*O = O'/I`");
* those two halves combine into the whole of 08M3's essential-image statement conditionally on the
  essential surjectivity of `pushforwardModuleFunctor i O`
  (`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_essSurj`).

What is proved here is that remaining hypothesis, `essSurj_pushforwardModuleFunctor`: for a closed
immersion `i` of topoi, every sheaf of `i_*O`-modules *is* a direct image. The argument is the
cheap one, which never mentions internal module objects. Since `i_*` is fully faithful the counit
`i^{-1}i_*O ⟶ O` is an isomorphism, and it is one of sheaves of *rings* (`ringCounit`,
`isIso_ringCounit_of_isEmbedding`). So for a sheaf `M` of `i_*O`-modules the inverse image
`i^{-1}M` is a sheaf of modules over `i^{-1}i_*O`, hence — by restriction of scalars along the
*inverse* of that ring isomorphism — a sheaf `F` of `O`-modules; and the unit `M ⟶ i_*i^{-1}M` is
an isomorphism because
`Stacks.Sheaves.PushforwardEssentialImage.moduleSheaf_mem_essImage_pushforward` puts the
underlying sheaf of **sets** of `M` in the essential image of `i_*`, where the unit of a fully
faithful right adjoint is invertible. Identifying `i_*i^{-1}M` with `i_*F` is the one place the
counit and the unit have to be compared, and that comparison is exactly the triangle identity of
`i^{-1} ⊣ i_*` (`ringSheafMap_ringUnit_eq`).

## Main definitions

* `Stacks.Sheaves.PushforwardEssentialImage.isoOfSheafHom`: a morphism of the underlying sheaves of
  sets which is an isomorphism and is additive and semilinear on sections is an isomorphism of
  sheaves of modules. The companion `isIso_of_isIso_moduleSheafFunctor_map` says that
  `Sheaf.moduleSheafFunctor` reflects isomorphisms.
* `Stacks.Sheaves.PushforwardEssentialImage.ringCounit`: the counit `f^{-1}f_*O ⟶ O` of a morphism
  of topoi, as a morphism of sheaves of rings between the transported ring structures.
* `Stacks.Sheaves.PushforwardEssentialImage.ringCounitInv`: its inverse, for an embedding of topoi;
  this is the ring isomorphism along which scalars are restricted below.
* `Stacks.Sheaves.PushforwardEssentialImage.directImageModulesObjIso`: the direct image of
  `f^{-1}f_*O`-modules read as `f_*O`-modules through the unit agrees with restriction of scalars
  along `ringCounitInv` followed by the Stacks 03D1 direct image.

## Main results

* `Stacks.Sheaves.PushforwardEssentialImage.ringSheafMap_ringUnit_eq`: the unit
  `f_*O ⟶ f_*f^{-1}f_*O` of `f^{-1} ⊣ f_*` at the direct-image ring is the direct image of the
  inverse of the ring-level counit. This is the triangle identity, and it is the only comparison
  the construction needs.
* `Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor`: for a closed
  immersion of topoi `f` and a sheaf of rings `O` on the source, every sheaf of modules over the
  direct-image ring `f_*O` is in the essential image of the Stacks 03D1 direct image. This is the
  hypothesis `hsurj` of `essImage_pushforwardModules_iff_of_essSurj`, discharged.
* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`:
  **the essential-image statement of Stacks 08M3**, unconditionally — a sheaf of `O'`-modules is a
  direct image exactly when the sectionwise kernel of the structure map annihilates it.
  `essImage_pushforwardModules_iff_of_epi_forget` is the same statement with Stacks' own
  surjectivity hypothesis, an epimorphism of the underlying sheaves of sets.

## Implementation notes

The closed-immersion hypothesis is spent in exactly two places, and nowhere else: through
`MorphismOfTopoi.IsEmbedding` (i.e. full faithfulness of `f_*`) it makes the counit invertible,
and through `IsClosedSubtopos` it puts the underlying sheaf of sets of a module over `f_*O` in the
essential image of `f_*`. Surjectivity of `i^#` is not used here at all; it enters 08M3 only
through the restriction-of-scalars half, which is where
`essImage_pushforwardModules_iff_of_essSurj` consumes it.

Three spelling points cost more than the mathematics:

* `Sheaf.ringSheaf (pushforwardRingSheaf f O)` and `f.pushforward.obj (Sheaf.ringSheaf O)` are
  definitionally but not syntactically equal, so a `rw` in a goal mixing them fails with "motive is
  not type correct". `ringSheafCounit` is therefore a `def` whose **ascribed result type** uses the
  `inverseImageRingSheaf` spelling; a type ascription on the term would not do, since the
  elaborator's `inferType` ignores it. Likewise `pushforwardRingCounitInvApp`, whose ascribed type
  is the one in which the scalar multiplication of a direct-image module is found by instance
  search.
* the two scalar multiplications compared in `directImageModulesObjIso` sit on definitionally equal
  types carrying two `Module` instances, so they are compared through
  `Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars` rather than by rewriting.
* `asIso` and `inv` are applied with their `IsIso` instance supplied positionally (`@asIso`,
  `@inv`), because instance search does not find an `IsIso` hypothesis that was obtained from a
  `MorphismOfTopoi.IsEmbedding` by projection.

`isIso_of_isIso_moduleSheafFunctor_map` is proved by hand rather than by a reflection instance:
Mathlib gives `SheafOfModules.toSheaf` only `Faithful`, and
`CategoryTheory.Sheaf.moduleSheafFunctor` is not known to reflect isomorphisms. The inverse is
built with `Stacks.Sheaves.RingedToposModules.ofSheafHom`, its additivity and semilinearity being
transported across the bijection on sections.

All five universes are free and independent: `u`, `v` for the source site, `u'`, `v'` for the
target site, and `w` for the sections of the structure sheaves and of the modules. The single
section universe `w` for both topoi is forced by `MorphismOfTopoi (Sheaf J (Type w))
(Sheaf K (Type w))`, which is what the Stacks 03D1 direct image of modules is stated for. The
rings are `RingCat`-valued rather than `CommRingCat`-valued, which is a generalization:
commutativity is used nowhere. The hypothesis `K.HasSheafCompose (forget RingCat.{w})` on the
*target* site is needed here although the conditional statement it discharges does not carry it,
because the inverse-image ring sheaf `f^{-1}f_*O` is formed from the underlying sheaf of sets of
`f_*O`; it is one of the standing instances of a morphism of ringed topoi.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe w v u v' u'

namespace Stacks.Sheaves.PushforwardEssentialImage

/-! ## Isomorphisms of sheaves of modules detected on the underlying sheaf of sets -/

section ReflectIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R}

/-- A morphism of sheaves of modules whose underlying morphism of sheaves of sets is an
isomorphism is itself an isomorphism: the inverse map on sections is additive and semilinear
because it is the two-sided inverse of a map which is.

Mathlib gives `SheafOfModules.toSheaf` only `CategoryTheory.Functor.Faithful`, so this is proved
directly from `Stacks.Sheaves.RingedToposModules.ofSheafHom` rather than by exhibiting
`Sheaf.moduleSheafFunctor` as a functor reflecting isomorphisms. -/
lemma isIso_of_isIso_moduleSheafFunctor_map (φ : M ⟶ N)
    (h : IsIso ((Sheaf.moduleSheafFunctor R).map φ)) : IsIso φ := by
  let _ := h
  have hsi : ∀ (X : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
      (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ))
        ((Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map φ) x) = x := by
    intro X x
    rw [← (Sheaf.sectionsFunctor J X).map_comp_apply, IsIso.hom_inv_id,
      (Sheaf.sectionsFunctor J X).map_id_apply]
  have his : ∀ (X : Cᵒᵖ) (y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R N)),
      (Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map φ)
        ((Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) y) = y := by
    intro X y
    rw [← (Sheaf.sectionsFunctor J X).map_comp_apply, IsIso.inv_hom_id,
      (Sheaf.sectionsFunctor J X).map_id_apply]
  have hadd : ∀ (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R N)),
      (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) (x + y) =
        (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) x +
          (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) y := by
    intro X x y
    refine (Function.LeftInverse.injective (hsi X)) ?_
    rw [Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_add, his, his, his]
  have hsmul : ∀ (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
      (y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R N)),
      (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) (r • y) =
        r • (Sheaf.sectionsFunctor J X).map (inv ((Sheaf.moduleSheafFunctor R).map φ)) y := by
    intro X r y
    refine (Function.LeftInverse.injective (hsi X)) ?_
    rw [Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul, his, his]
  refine ⟨ofSheafHom (inv ((Sheaf.moduleSheafFunctor R).map φ)) hadd hsmul,
    hom_ext_moduleSheafFunctor ?_, hom_ext_moduleSheafFunctor ?_⟩ <;>
  rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_ofSheafHom,
    CategoryTheory.Functor.map_id] <;> simp

/-- An isomorphism of the underlying sheaves of sets which is additive and compatible with scalar
multiplication on sections over every object of the site is an isomorphism of sheaves of modules.

The `IsIso` argument is explicit rather than an instance: at the use site below the morphism is an
identity read across a definitional equality of objects, and leaving the instance to be synthesized
there is what makes the elaborator unfold the comparison a second time. -/
noncomputable def isoOfSheafHom (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (hs : IsIso s)
    (hadd : ∀ (X : Cᵒᵖ) (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
      (Sheaf.sectionsFunctor J X).map s (x + y) =
        (Sheaf.sectionsFunctor J X).map s x + (Sheaf.sectionsFunctor J X).map s y)
    (hsmul : ∀ (X : Cᵒᵖ) (r : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R))
      (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf R M)),
      (Sheaf.sectionsFunctor J X).map s (r • x) = r • (Sheaf.sectionsFunctor J X).map s x) :
    M ≅ N :=
  @asIso _ _ _ _ (ofSheafHom s hadd hsmul)
    (isIso_of_isIso_moduleSheafFunctor_map (ofSheafHom s hadd hsmul)
      (by rw [moduleSheafFunctor_map_ofSheafHom]; exact hs))

end ReflectIso

/-! ## The counit of `f⁻¹ ⊣ f_*` as an isomorphism of sheaves of rings -/

section RingCounit

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (O : Sheaf J RingCat.{w})

/-- The counit `f⁻¹f_*O ⟶ O` at the underlying sheaf of sets of `O`, with its domain written in
the `inverseImageRingSheaf` spelling.

This must be a `def` with an ascribed result type. The domain is definitionally but not
syntactically `f.inverseImage.obj (f.pushforward.obj (Sheaf.ringSheaf O))`, and a goal mixing the
two spellings is inaccessible to `rw`, which reports "motive is not type correct". -/
noncomputable def ringSheafCounit :
    Sheaf.ringSheaf (inverseImageRingSheaf f (pushforwardRingSheaf f O)) ⟶ Sheaf.ringSheaf O :=
  f.adj.counit.app (Sheaf.ringSheaf O)

/-- The underlying morphism of sheaves of sets of the ring-level counit is the counit of
`f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `O`. -/
lemma ringSheafMap_ringCounit :
    (sheafCompose J (forget RingCat.{w})).map (ringCounit f O) = ringSheafCounit f O :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- For an embedding of topoi the counit at the underlying sheaf of sets of `O` is an
isomorphism. -/
lemma isIso_ringSheafCounit (hf : f.IsEmbedding) : IsIso (ringSheafCounit f O) :=
  (MorphismOfTopoi.isEmbedding_iff_isIso_counit_app f).mp hf _

/-- For an embedding of topoi the counit `f⁻¹f_*O ⟶ O` is an isomorphism of sheaves of rings: it is
one on underlying sheaves of sets, and `sheafCompose J (forget RingCat)` reflects isomorphisms. -/
lemma isIso_ringCounit_of_isEmbedding (hf : f.IsEmbedding) : IsIso (ringCounit f O) := by
  have h : IsIso ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O)) := by
    rw [ringSheafMap_ringCounit]
    exact isIso_ringSheafCounit f O hf
  exact isIso_of_reflects_iso (ringCounit f O) (sheafCompose J (forget RingCat.{w}))

/-- The inverse `O ⟶ f⁻¹f_*O` of the ring-level counit of an embedding of topoi. -/
noncomputable def ringCounitInv (hf : f.IsEmbedding) :
    O ⟶ inverseImageRingSheaf f (pushforwardRingSheaf f O) :=
  @inv _ _ _ _ (ringCounit f O) (isIso_ringCounit_of_isEmbedding f O hf)

/-- The inverse of the ring-level counit followed by the counit is the identity of `O`. -/
lemma ringCounitInv_comp (hf : f.IsEmbedding) :
    ringCounitInv f O hf ≫ ringCounit f O = 𝟙 O :=
  @IsIso.inv_hom_id _ _ _ _ (ringCounit f O) (isIso_ringCounit_of_isEmbedding f O hf)

/-- The unit `f_*O ⟶ f_*f⁻¹f_*O` of `f⁻¹ ⊣ f_*` at the direct-image sheaf of rings is, on
underlying sheaves of sets, the direct image of the inverse of the ring-level counit. -/
lemma ringSheafMap_ringUnit_eq (hf : f.IsEmbedding) :
    (sheafCompose K (forget RingCat.{w})).map (ringUnit f (pushforwardRingSheaf f O)) =
      f.pushforward.map ((sheafCompose J (forget RingCat.{w})).map (ringCounitInv f O hf)) := by
  have hc := isIso_ringSheafCounit f O hf
  have htri : f.adj.unit.app (Sheaf.ringSheaf (pushforwardRingSheaf f O)) ≫
      f.pushforward.map (ringSheafCounit f O) =
        𝟙 (Sheaf.ringSheaf (pushforwardRingSheaf f O)) :=
    f.adj.right_triangle_components (Sheaf.ringSheaf O)
  have h1 : (sheafCompose J (forget RingCat.{w})).map (ringCounitInv f O hf) ≫
      ringSheafCounit f O = 𝟙 (Sheaf.ringSheaf O) := by
    rw [← ringSheafMap_ringCounit f O, ← CategoryTheory.Functor.map_comp, ringCounitInv_comp,
      CategoryTheory.Functor.map_id]
  have h3 : f.pushforward.map ((sheafCompose J (forget RingCat.{w})).map (ringCounitInv f O hf)) ≫
      f.pushforward.map (ringSheafCounit f O) =
        𝟙 (f.pushforward.obj (Sheaf.ringSheaf O)) := by
    rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_id]
  rw [ringSheafMap_ringUnit]
  refine (cancel_mono (f.pushforward.map (ringSheafCounit f O))).mp ?_
  exact htri.trans h3.symm

end RingCounit

/-! ## Essential surjectivity of the direct image of modules along a closed immersion -/

section EssSurj

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (O : Sheaf J RingCat.{w}) (hf : f.IsEmbedding)
  (N : SheafOfModules.{w} (inverseImageRingSheaf f (pushforwardRingSheaf f O)))

/-- The scalar `κ(r)` pushed forward, where `κ : O ⟶ f⁻¹f_*O` is `ringCounitInv`.

This must be a `def` with an ascribed result type: the type written here is the one in which the
scalar multiplication of a direct image of modules is found by instance search, while the
`f.pushforward ⋙ Sheaf.sectionsFunctor` spelling of the same type — which is what the term has —
leaves `HSMul` unsynthesizable. -/
noncomputable def pushforwardRingCounitInvApp (X : Dᵒᵖ)
    (r : (pushforwardRingSheaf f O).obj.obj X) :
    (pushforwardRingSheaf f (inverseImageRingSheaf f (pushforwardRingSheaf f O))).obj.obj X :=
  (f.pushforward ⋙ Sheaf.sectionsFunctor K X).map
    ((sheafCompose J (forget RingCat.{w})).map (ringCounitInv f O hf)) r

/-- `ringSheafMap_ringUnit_eq` read on a section: the unit acts on a section of `f_*O` as the
direct image of `κ` does. -/
lemma ringUnit_app_eq (X : Dᵒᵖ) (r : (pushforwardRingSheaf f O).obj.obj X) :
    ((ringUnit f (pushforwardRingSheaf f O)).hom.app X).hom r =
      pushforwardRingCounitInvApp f O hf X r :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor K X).map m r) (ringSheafMap_ringUnit_eq f O hf)

/-- Scalar multiplication on the direct image of an `f⁻¹f_*O`-module read as an `f_*O`-module: a
scalar acts through the unit `f_*O ⟶ f_*f⁻¹f_*O`. This is restriction of scalars, so it holds by
definition. -/
lemma smul_directImageModules (X : Dᵒᵖ) (r : (pushforwardRingSheaf f O).obj.obj X)
    (x : ((directImageModules f (pushforwardRingSheaf f O)).obj N).val.obj X) :
    r • x =
      (((ringUnit f (pushforwardRingSheaf f O)).hom.app X).hom r) •
        (show ((pushforwardModuleFunctor f
          (inverseImageRingSheaf f (pushforwardRingSheaf f O))).obj N).val.obj X from x) := rfl

/-- Scalar multiplication on the Stacks 03D1 direct image of the restriction of scalars of an
`f⁻¹f_*O`-module along `κ`: a scalar acts through the direct image of `κ`. -/
lemma smul_pushforwardRestrictScalars (X : Dᵒᵖ)
    (r : (pushforwardRingSheaf f O).obj.obj X)
    (x : ((pushforwardModuleFunctor f O).obj
      ((SheafOfModules.restrictScalars (ringCounitInv f O hf)).obj N)).val.obj X) :
    r • x =
      (pushforwardRingCounitInvApp f O hf X r) •
        (show ((pushforwardModuleFunctor f
          (inverseImageRingSheaf f (pushforwardRingSheaf f O))).obj N).val.obj X from x) :=
  moduleSMulObj_restrictScalars (ringCounitInv f O hf) N
    (f.pushforward ⋙ Sheaf.sectionsFunctor K X) r x

/-- **The two routes from an `f⁻¹f_*O`-module to an `f_*O`-module agree.** Taking the Stacks 03D3
direct image and restricting scalars along the unit gives the same sheaf of `f_*O`-modules as
restricting scalars along `κ = ringCounitInv` and taking the Stacks 03D1 direct image.

The underlying sheaves of sets are definitionally equal, so the isomorphism is the identity there;
its content is that the two scalar multiplications agree, which by the two lemmas above is the
single scalar identity `ringUnit_app_eq`, i.e. the triangle identity. -/
noncomputable def directImageModulesObjIso :
    (directImageModules f (pushforwardRingSheaf f O)).obj N ≅
      (pushforwardModuleFunctor f O).obj
        ((SheafOfModules.restrictScalars (ringCounitInv f O hf)).obj N) :=
  isoOfSheafHom (R := pushforwardRingSheaf f O)
      (M := (directImageModules f (pushforwardRingSheaf f O)).obj N)
      (N := (pushforwardModuleFunctor f O).obj
        ((SheafOfModules.restrictScalars (ringCounitInv f O hf)).obj N))
      (𝟙 _) (IsIso.id _) (fun _ _ _ ↦ rfl) (fun X r x ↦
    ((smul_directImageModules f O N X r x).trans
        (congrArg (fun z ↦ z •
            (show ((pushforwardModuleFunctor f
              (inverseImageRingSheaf f (pushforwardRingSheaf f O))).obj N).val.obj X from x))
          (ringUnit_app_eq f O hf X r))).trans
      (smul_pushforwardRestrictScalars f O hf N X r x).symm)

end EssSurj

/-! ## Stacks 08M3: the essential image of the direct image of modules -/

section Main

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (O : Sheaf J RingCat.{w})

/-- **Every sheaf of modules over the direct-image ring is a direct image.** For a closed immersion
of topoi `f` and a sheaf of rings `O` on the source, the Stacks 03D1 direct image
`Mod(O) ⥤ Mod(f_*O)` is essentially surjective.

This is the hypothesis `hsurj` of
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_essSurj`. The
preimage of `M` is the inverse image `f⁻¹M`, a sheaf of modules over `f⁻¹f_*O`, with scalars
restricted along the inverse of the ring-level counit; and the unit `M ⟶ f_*f⁻¹M` is an
isomorphism because
`moduleSheaf_mem_essImage_pushforward` puts the underlying sheaf of sets of `M` in the essential
image of the fully faithful `f_*`, where
`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage` applies. No surjectivity of a structure
map is used. -/
theorem essSurj_pushforwardModuleFunctor (hfc : MorphismOfTopoi.IsClosedImmersion f)
    (M : SheafOfModules.{w} (pushforwardRingSheaf f O)) :
    (pushforwardModuleFunctor f O).essImage M := by
  have hemb := hfc.1
  have := hemb.full
  have := hemb.faithful
  have hunit : IsIso (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) M)) :=
    (f.adj.isIso_unit_app_iff_mem_essImage).mpr
      (moduleSheaf_mem_essImage_pushforward hfc M)
  have hθ : (Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O)).map
        (toposModulesHomEquiv f (pushforwardRingSheaf f O) M
          ((inverseImageModules f (pushforwardRingSheaf f O)).obj M)
          (𝟙 ((inverseImageModules f (pushforwardRingSheaf f O)).obj M))) =
      f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) M) := by
    rw [moduleSheafFunctor_map_toposModulesHomEquiv, CategoryTheory.Functor.map_id]
    exact f.adj.homEquiv_id _
  have hiso : IsIso (toposModulesHomEquiv f (pushforwardRingSheaf f O) M
      ((inverseImageModules f (pushforwardRingSheaf f O)).obj M)
      (𝟙 ((inverseImageModules f (pushforwardRingSheaf f O)).obj M))) :=
    isIso_of_isIso_moduleSheafFunctor_map _ (by rw [hθ]; exact hunit)
  exact ⟨_, ⟨((@asIso _ _ _ _ _ hiso).trans
    (directImageModulesObjIso f O hemb
      ((inverseImageModules f (pushforwardRingSheaf f O)).obj M))).symm⟩⟩

/-- **Stacks 08M3, the essential-image statement.** Let `i : (Sh(C), O) → (Sh(D), O')` be a
morphism of ringed topoi whose underlying morphism of topoi is a closed immersion and whose
structure map `i^# : O' ⟶ i_*O` is locally surjective, and let `I ⊆ O'` be the sectionwise kernel
of `i^#`. Then a sheaf of `O'`-modules is in the essential image of the direct image
`i_* : Mod(O) ⥤ Mod(O')` exactly when `I` annihilates it.

The forward implication needs neither hypothesis on `i`
(`smul_eq_zero_of_essImage_pushforwardModules`); the reverse one spends local surjectivity in
`Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero` and the
closed-immersion hypothesis in `essSurj_pushforwardModuleFunctor`. -/
@[stacks 08M3 "essential_image"]
theorem essImage_pushforwardModules_iff_of_isClosedImmersion
    (hfc : MorphismOfTopoi.IsClosedImmersion f) {O' : Sheaf K RingCat.{w}}
    (fSharp : O' ⟶ pushforwardRingSheaf f O) [Sheaf.IsLocallySurjective fSharp]
    (G : SheafOfModules.{w} O') :
    (pushforwardModules f O fSharp).essImage G ↔
      ∀ (X : Dᵒᵖ) (a : O'.obj.obj X), a ∈ RingHom.ker (fSharp.hom.app X).hom →
        ∀ m : G.val.obj X, a • m = 0 :=
  essImage_pushforwardModules_iff_of_essSurj fSharp (essSurj_pushforwardModuleFunctor f O hfc) G

/-- **Stacks 08M3, the essential-image statement, with Stacks' own surjectivity hypothesis.** The
source says "surjective" of `i^#`, which for sheaves means an epimorphism of the underlying sheaves
of sets; `Stacks.SheafOfModules.ChangeOfRings.isLocallySurjective_of_epi_forget` converts that into
the local surjectivity used by
`essImage_pushforwardModules_iff_of_isClosedImmersion`. `HasSheafify K (Type w)` is not part of the
Stacks hypothesis — it is what factoring an epimorphism through its image sheaf needs, and it is
automatic for a small site. -/
theorem essImage_pushforwardModules_iff_of_epi_forget [HasSheafify K (Type w)]
    (hfc : MorphismOfTopoi.IsClosedImmersion f) {O' : Sheaf K RingCat.{w}}
    (fSharp : O' ⟶ pushforwardRingSheaf f O)
    (hepi : Epi ((sheafCompose K (forget RingCat.{w})).map fSharp))
    (G : SheafOfModules.{w} O') :
    (pushforwardModules f O fSharp).essImage G ↔
      ∀ (X : Dᵒᵖ) (a : O'.obj.obj X), a ∈ RingHom.ker (fSharp.hom.app X).hom →
        ∀ m : G.val.obj X, a • m = 0 :=
  have := Stacks.SheafOfModules.ChangeOfRings.isLocallySurjective_of_epi_forget fSharp hepi
  essImage_pushforwardModules_iff_of_isClosedImmersion f O hfc fSharp G

end Main

end Stacks.Sheaves.PushforwardEssentialImage

end
