module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomFromUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Product
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomUnitVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseChangeFirstCohomology

/-!
# The first étale cohomology of an internal hom on an affine scheme

Let `T` be an affine scheme and let `𝓕` and `𝓖` be `𝒪`-modules on the small étale site of `T`.
If `𝓕` is locally projective, then the first cohomology of the internal hom
`𝓗 = 𝓗om_𝒪(𝓕, 𝓖)` vanishes.

The argument is the one of the source.  Local projectivity of `𝓕` is a statement about the
corresponding module on `T_Zar`, and on an affine scheme a locally projective quasi-coherent
module is a direct summand of a free module; the associated-module functor carries that
decomposition to the small étale site, where it exhibits `𝓕` as a direct summand of a free
`𝒪`-module.  Internal hom turns the coproduct `⊕_{i ∈ I} 𝒪` in its first variable into the
product `∏_{i ∈ I} 𝓗om_𝒪(𝒪, 𝓖)`, the first extension groups out of a fixed object inject into
the product of the first extension groups, and vanishing of cohomology passes to a direct
summand.  What is left over is the first cohomology of `𝓗om_𝒪(𝒪, 𝓖)`, which is the universe
lift of `𝓖`; that is discharged by
`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_unit`, so **both
registrations below are unconditional**.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafHomFunctor`: the internal hom into a fixed target on the
  small étale site, contravariant in its source, valued in abelian sheaves.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_of_retract`: the first
  cohomology of the internal hom out of a direct summand of a free module vanishes as soon as
  it vanishes for the internal hom out of the structure sheaf.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_unit`: the vanishing for the
  internal hom out of the structure sheaf, which is the source's `H^1` of a product of
  quasi-coherent modules.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_associatedModule`: **Stacks
  061J** for the module associated to a locally projective quasi-coherent module on `T_Zar`.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_of_isLocallyProjective`:
  **Stacks 061J** for quasi-coherent `𝒪`-modules on `T_étale` the first of which restricts to a
  locally projective module on `T_Zar`.

Both of the last two ask the *target* `𝓖` to be quasi-coherent on the site as well, which is the
source's own hypothesis; see "Why `𝓖` has to be quasi-coherent" below.

## The input from Stacks 03DW, and how it is discharged

The one thing the argument above does not itself supply is the vanishing of the first
cohomology of `𝓗om_𝒪(𝒪, 𝓖)`, the internal hom out of the structure sheaf, the input of Stacks 03DW
together with Stacks 01XB.  It is proved, as
`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_toSheafSheafHomUnit`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleInternalHomUnitVanishing.lean`), from
which `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_unit` below is read off,
and the two registrations below are unconditional.  Only
`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_of_retract` still takes it, as it
must: that statement asks nothing of `T` or of `𝓖`, so there is nothing there to prove it from.

The proof has three steps.

* **The site.** Stacks 03DW clause (2) is proved on Mathlib's
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, whereas this file works on the size-bounded
  site `AlgebraicGeometry.SmallEtale` of Stacks 021B.  That gap is closed by
  `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_boundedSmallEtale_of_smallEtale_sheaf`,
  which transports the vanishing of `CategoryTheory.Sheaf.H` between the two sites for an
  arbitrary abelian sheaf.
* **The coefficient universe.**  The module universe of
  `AlgebraicGeometry.SmallEtale.sheafHom` is one above that of its arguments, so the cohomology
  here is at coefficients `AddCommGrpCat.{u + 1}` while the known vanishing is at
  `AddCommGrpCat.{u}`; `CategoryTheory.Sheaf.H'`, through which every existing statement routes,
  has no coefficient-universe parameter at all.  The universe-lifting functor on abelian groups
  is fully faithful but **not essentially surjective**; essential surjectivity is, however, not
  what a comparison of `Ext` needs.
  `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` asks for an
  exact, fully faithful, injectivity-preserving functor out of a category with enough
  injectives, and `CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor` is one on any site
  with a small dense subsite.  The passage is
  `Stacks.Sheaves.UniverseLift.subsingleton_H_uliftFunctor_of_subsingleton_H`, specialised to
  the small étale site as `AlgebraicGeometry.subsingleton_H_uliftFunctor_smallEtale`.
* **The unit-source internal hom.**  `𝓗om_𝒪(𝒪, 𝓖)` is the universe lift of `𝓖` — not `𝓖`
  itself, which is why the unit isomorphisms of this tree (`unitInternalHomIso` and its
  relatives) do not apply: they tie the module universe to the ring universe.  The isomorphism
  to use is `AlgebraicGeometry.SmallEtale.toSheafSheafHomUnitIso`.

The source's step `𝓕 = (𝓕_Zar)^a` is *not* a hypothesis here.  The predicate
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule` is a theorem,
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean`), proved
unconditionally for an arbitrary scheme by the counit argument there and registered against Tag
03DX, so the general form discharges it inline.

Note that essential surjectivity at `τ = étale` does **not** go through the effectivity of fpqc
descent, Stacks 023T: the counit route proves it from Stacks 0GN7 at the Zariski site plus
cartesianness of quasi-coherent modules between affine objects.  023T is what the *big* fppf
site still needs, through the homonymous
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/QuasicoherentColimitsOfSize.lean`),
which is a different predicate on a different site.

## Why `𝓖` has to be quasi-coherent

Stacks 061J assumes `𝓖` quasi-coherent, and the hypothesis cannot be dropped: for an arbitrary
`𝓖` on the small étale site of an affine scheme the first cohomology of `𝓗om_𝒪(𝒪, 𝓖)` is **not**
zero, so at that generality the input from Stacks 03DW is false.  `[G.IsQuasicoherentOnSite]` is
asked of both registered statements, which is exactly the source's hypothesis and so loses
nothing.

With it, the vanishing that gets transported is
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`, through
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` which writes `𝓖` as an
`Mᵃ`.  Quasi-coherence of `𝓖` is therefore not a convenience: it is what makes `𝓖` an `Mᵃ` at
all, and so what makes the Zariski-side input applicable.


## Implementation notes

The module universe of the internal hom is one above that of its arguments, so the cohomology
here is `CategoryTheory.Sheaf.H` with coefficients in `AddCommGrpCat.{u + 1}`, whose `Ext`
universe is free.  `CategoryTheory.Sheaf.H'` and the vanishing statements for a product of
abelian sheaves are pinned to the morphism universe of the site and do not apply.

`subsingleton_ext_one_of_isLimit` is the form of Stacks 060L the argument needs: it is the
degree-one half of `CategoryTheory.Abelian.mono_piComparison_extFunctorObj_one` stated for an
arbitrary limit fan rather than for the chosen product, so that no product of extension groups
is required to exist in the free `Ext` universe.

## References

* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 060L](https://stacks.math.columbia.edu/tag/060L)
* [Stacks Project, Tag 060R](https://stacks.math.columbia.edu/tag/060R)
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v₁ u₁ u w

namespace AlgebraicGeometry.SmallEtale

/-! ### Cohomology of a direct summand and extension groups into a limit -/

/-- **Vanishing of sheaf cohomology passes to a direct summand.**  Cohomology in a fixed degree
is a functor, so a split monomorphism of abelian sheaves induces a split monomorphism of
cohomology groups, and a group that embeds into a trivial group is trivial. -/
private theorem subsingleton_sheafH_of_retract {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{t}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] {F G : Sheaf J AddCommGrpCat.{t}}
    (i : F ⟶ G) (p : G ⟶ F) (hip : i ≫ p = 𝟙 F) (n : ℕ)
    (hG : Subsingleton (Sheaf.H.{w} G n)) :
    Subsingleton (Sheaf.H.{w} F n) := by
  refine ⟨fun x y => ?_⟩
  simpa only [← Sheaf.H.map_comp_apply, hip, Sheaf.H.map_id_apply] using
    congrArg (Sheaf.H.map p n) (hG.elim (Sheaf.H.map i n x) (Sheaf.H.map i n y))

/-- **The first extension groups out of a fixed object take a limit of a family to a
subobject of nothing.**  An extension of `X` by the limit of a family whose pushforward along
every projection splits admits a retraction of its inclusion, assembled from the retractions of
the pushforwards through the universal property, hence splits itself. -/
private theorem subsingleton_ext_one_of_isLimit {D : Type u₁} [Category.{v₁} D] [Abelian D]
    [HasExt.{w} D] {I : Type t} (objects : I → D) (fan : Fan objects) (hfan : IsLimit fan)
    (X : D) (hvan : ∀ i, Subsingleton (Abelian.Ext.{w} X (objects i) 1)) :
    Subsingleton (Abelian.Ext.{w} X fan.pt 1) := by
  classical
  refine subsingleton_of_forall_eq 0 fun e => ?_
  obtain ⟨M, incl, proj, hzero, hse, rfl⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum D X fan.pt).1 e
  have lifts (i : I) : ∃ r : M ⟶ objects i, incl ≫ r = fan.proj i := by
    obtain ⟨b, hb⟩ := Abelian.Ext.contravariant_sequence_exact₁ hse (objects i)
      (Abelian.Ext.mk₀ (fan.proj i)) (add_zero 1) (Subsingleton.elim _ _)
    exact ⟨Abelian.Ext.homEquiv₀ b, (Abelian.Ext.mk₀_bijective _ _).1
      (by rwa [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply])⟩
  let retraction := hfan.lift (Fan.mk M (fun i => (lifts i).choose))
  have hsplit : incl ≫ retraction = 𝟙 fan.pt := hfan.hom_ext fun i => by
    simp only [Category.assoc, retraction, IsLimit.fac, Category.id_comp]
    exact (lifts i.as).choose_spec
  have hclass := congrArg
    (fun c => c.comp (Abelian.Ext.mk₀ retraction) (add_zero 1)) hse.extClass_comp
  rwa [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hsplit,
    Abelian.Ext.comp_mk₀_id, Abelian.Ext.zero_comp] at hclass

/-! ### The internal hom as a contravariant functor into abelian sheaves -/

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- **`𝓗om_𝒪(-, 𝓖)` on the small étale site of `T`**, as a functor from the opposite category of
sheaves of modules to abelian sheaves: a morphism `𝓕' ⟶ 𝓕` acts on a local morphism
`𝓕|_U ⟶ 𝓖|_U` by precomposition. -/
public def sheafHomFunctor (G : SheafOfModules.{u} (structureSheaf B T hT)) :
    (SheafOfModules.{u} (structureSheaf B T hT))ᵒᵖ ⥤
      Sheaf (topology B T hT) AddCommGrpCat.{u + 1} where
  obj F := ⟨(homPresheaf B T hT F.unop.val G.val).presheaf,
    homPresheaf_isSheaf B T hT F.unop.val G⟩
  map f := ⟨{
    app U := AddCommGrpCat.ofHom
      { toFun := fun α =>
          (restrFun (commStructurePresheaf B T hT) U.unop).map f.unop.val ≫ α
        map_zero' := rfl
        map_add' _ _ := rfl }
    naturality _ _ _ := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro α
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl }⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sections of `𝓗om_𝒪(𝓕, 𝓖)` over an object `U` of the small étale site are the morphisms
`𝓕|_U ⟶ 𝓖|_U` of `𝒪|_U`-modules, naturally in `𝓕`. -/
private def sheafHomFunctorEvaluationIso (G : SheafOfModules.{u} (structureSheaf B T hT))
    (U : SmallEtale B T hT) :
    sheafHomFunctor B T hT G ⋙ sheafToPresheaf (topology B T hT) AddCommGrpCat.{u + 1} ⋙
        (evaluation (SmallEtale B T hT)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op U) ≅
      (SheafOfModules.overFunctor (structureSheaf B T hT) U).op ⋙
        preadditiveYoneda.obj (G.over U) :=
  NatIso.ofComponents
    (fun F => AddEquiv.toAddCommGrpIso
      { toFun := fun α => ⟨α⟩
        invFun := fun α => α.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
    (by
      intro F F' f
      ext α
      rfl)

/-- **Stacks 03EN in the first variable, on the small étale site of `T`.**  The internal hom
into a fixed target carries a coproduct of sheaves of modules to a product of internal homs:
restriction to a localization of the site is a left adjoint, so it preserves the coproduct, and
the morphisms out of a coproduct are the product of the morphisms out of its terms. -/
private def isLimitFanSheafHomFunctor (G : SheafOfModules.{u} (structureSheaf B T hT))
    {I : Type u} {objects : I → SheafOfModules.{u} (structureSheaf B T hT)}
    (cofan : Cofan objects) (hc : IsColimit cofan) :
    IsLimit (Fan.mk ((sheafHomFunctor B T hT G).obj (op cofan.pt))
      (fun i => (sheafHomFunctor B T hT G).map (cofan.inj i).op)) := by
  let K := sheafHomFunctor B T hT G
  let : PreservesLimitsOfShape (Discrete I)
      (K ⋙ sheafToPresheaf (topology B T hT) AddCommGrpCat.{u + 1}) := by
    apply preservesLimitsOfShape_of_evaluation
    intro U
    have : PreservesColimitsOfSize.{u, u}
        (SheafOfModules.overFunctor (structureSheaf B T hT) U.unop :
          SheafOfModules.{u} (structureSheaf B T hT) ⥤
            SheafOfModules.{u} ((structureSheaf B T hT).over U.unop)) :=
      (SheafOfModules.overPushforwardOverAdj
        (R := structureSheaf B T hT) U.unop).leftAdjoint_preservesColimits
    have : PreservesLimitsOfShape (Discrete I)
        (SheafOfModules.overFunctor (structureSheaf B T hT) U.unop :
          SheafOfModules.{u} (structureSheaf B T hT) ⥤
            SheafOfModules.{u} ((structureSheaf B T hT).over U.unop)).op :=
      preservesLimitsOfShape_op _ _
    have : PreservesLimitsOfSize.{u, u} (preadditiveYoneda.obj (G.over U.unop)) :=
      preservesLimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact preservesLimitsOfShape_of_natIso (sheafHomFunctorEvaluationIso B T hT G U.unop).symm
  let : PreservesLimitsOfShape (Discrete I) K :=
    preservesLimitsOfShape_of_reflects_of_preserves K
      (sheafToPresheaf (topology B T hT) AddCommGrpCat.{u + 1})
  exact (Fan.isLimitMapConeEquiv K _ cofan.op).1
    (isLimitOfPreserves K (Cofan.IsColimit.op hc))

/-! ### The vanishing -/

variable [HasSheafify (topology B T hT) AddCommGrpCat.{u + 1}]
  [HasExt.{w} (Sheaf (topology B T hT) AddCommGrpCat.{u + 1})]

/-- **The first cohomology of the internal hom out of a direct summand of a free module
vanishes**, as soon as it vanishes for the internal hom out of the structure sheaf.  A free
module is a coproduct of copies of the structure sheaf, so the internal hom out of it is a
product of copies of `𝓗om_𝒪(𝒪, 𝓖)`; the first extension groups out of a fixed object inject
into the product of the first extension groups, and vanishing passes to a direct summand. -/
public theorem subsingleton_sheafH_one_sheafHom_of_retract
    (F G : SheafOfModules.{u} (structureSheaf B T hT)) (I : Type u)
    (r : Retract F (SheafOfModules.free I))
    (h03DW : Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        (sheafHom B T hT (SheafOfModules.unit (structureSheaf B T hT)) G)) 1)) :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj (sheafHom B T hT F G)) 1) := by
  let K := sheafHomFunctor B T hT G
  have hfree : Subsingleton (Sheaf.H.{w} (K.obj (op (SheafOfModules.free I))) 1) :=
    subsingleton_ext_one_of_isLimit _ _
      (isLimitFanSheafHomFunctor B T hT G (SheafOfModules.freeCofan I)
        (SheafOfModules.isColimitFreeCofan I)) _ (fun _ => h03DW)
  refine subsingleton_sheafH_of_retract (K.map r.r.op) (K.map r.i.op) ?_ 1 hfree
  rw [← K.map_comp, ← op_comp, r.retract, op_id, K.map_id]

/-- **The first cohomology of the internal hom out of the structure sheaf vanishes** on an
affine scheme, for a quasi-coherent `𝒪`-module `𝓖` on the small étale site.  This is the step of
the source which reads `H^1(T_étale, ∏_{i ∈ I} 𝓖) = 0` because the cohomology of a
quasi-coherent sheaf on an affine scheme vanishes, Stacks 03DW with Stacks 01XB.

It is `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_toSheafSheafHomUnit` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleInternalHomUnitVanishing.lean`, which
identifies `𝓗om_𝒪(𝒪, 𝓖)` with the universe lift of `𝓖` by
`AlgebraicGeometry.SmallEtale.toSheafSheafHomUnitIso` and writes `𝓖` as an `Mᵃ` by Stacks 03DX
part (2) at `τ = étale`. -/
public theorem subsingleton_sheafH_one_sheafHom_unit [AlgebraicGeometry.IsAffine T]
    (G : SheafOfModules.{u} (structureSheaf B T hT)) [G.IsQuasicoherentOnSite] :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        (sheafHom B T hT (SheafOfModules.unit (structureSheaf B T hT)) G)) 1) :=
  subsingleton_sheafH_one_toSheafSheafHomUnit B T hT G

/-- **The first cohomology of the internal hom out of a retract of an associated module
vanishes.**  A locally projective quasi-coherent module on an affine scheme is a direct summand
of a free module, and the associated-module functor carries that decomposition to the small
étale site, where it takes a free module to a free module. -/
private theorem subsingleton_sheafH_one_sheafHom_of_retract_associatedModule
    [AlgebraicGeometry.IsAffine T] (M : T.Modules) [M.IsQuasicoherent]
    (hM : Scheme.Modules.IsLocallyProjective M) (F G : SheafOfModules.{u} (structureSheaf B T hT))
    [G.IsQuasicoherentOnSite] (r : Retract F ((associatedModule B T hT).obj M)) :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj (sheafHom B T hT F G)) 1) := by
  obtain ⟨I, ⟨r'⟩⟩ := Scheme.Modules.exists_retract_free_of_isLocallyProjective T M hM
  exact subsingleton_sheafH_one_sheafHom_of_retract B T hT F G I
    (r.trans ((r'.map (associatedModule B T hT)).trans
      (Retract.ofIso (SheafOfModules.pullbackObjFreeIso (structureMap B T hT) I))))
    (subsingleton_sheafH_one_sheafHom_unit B T hT G)

/-- **Stacks 061J for an associated module.**  Let `T` be an affine scheme and let `M` be a
locally projective quasi-coherent `𝒪_T`-module.  The first cohomology of the internal hom from
the associated module `M^a` to an `𝒪`-module `𝓖` on the small étale site of `T` vanishes. -/
@[stacks 061J]
public theorem subsingleton_sheafH_one_sheafHom_associatedModule
    [AlgebraicGeometry.IsAffine T] (M : T.Modules)
    [M.IsQuasicoherent] (hM : Scheme.Modules.IsLocallyProjective M)
    (G : SheafOfModules.{u} (structureSheaf B T hT)) [G.IsQuasicoherentOnSite] :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        (sheafHom B T hT ((associatedModule B T hT).obj M) G)) 1) := by
  exact subsingleton_sheafH_one_sheafHom_of_retract_associatedModule B T hT M hM _ G
    (Retract.refl _)

/-- **Stacks 061J.**  Let `T` be an affine scheme and let `𝓕` and `𝓖` be quasi-coherent
`𝒪`-modules on the small étale site of `T`.  If `𝓕` is locally projective — that is, if its
restriction to the small Zariski site of `T` is a locally projective `𝒪_T`-module, which is what
Stacks 060R defines local projectivity to mean — then the first cohomology of the internal hom
`𝓗om_𝒪(𝓕, 𝓖)` vanishes. -/
@[stacks 061J]
public theorem subsingleton_sheafH_one_sheafHom_of_isLocallyProjective
    [AlgebraicGeometry.IsAffine T]
    (F G : SheafOfModules.{u} (structureSheaf B T hT)) [F.IsQuasicoherentOnSite]
    [G.IsQuasicoherentOnSite]
    (hF : Scheme.Modules.IsLocallyProjective ((restrictModule B T hT).obj F)) :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj (sheafHom B T hT F G)) 1) := by
  obtain ⟨M, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B T hT F inferInstance
  have : IsIso ((associatedModuleAdjunction B T hT).unit.app M.obj) :=
    unitIsoOnQuasicoherent B T hT M
  have : M.obj.IsQuasicoherent := M.property
  have hM : Scheme.Modules.IsLocallyProjective M.obj :=
    Scheme.Modules.isLocallyProjective_of_iso
      (((restrictModule B T hT).mapIso e).symm ≪≫
        (asIso ((associatedModuleAdjunction B T hT).unit.app M.obj)).symm) hF
  exact subsingleton_sheafH_one_sheafHom_of_retract_associatedModule B T hT M.obj hM F G
    (Retract.ofIso e.symm)

end AlgebraicGeometry.SmallEtale

end
