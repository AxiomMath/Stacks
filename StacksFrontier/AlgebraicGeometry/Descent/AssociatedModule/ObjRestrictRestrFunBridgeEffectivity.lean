module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjRestrictRestrFunBridge
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional

/-!
# From the effectivity of the descent datum of Stacks 03DX (1) to the local isomorphisms

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlueDescentDatumViaUnprimed.lean` builds
the quasi-coherent descent datum of Stacks 03DX (1),
`AlgebraicGeometry.BigFppfOver.memberQcohDatum`, for the family of structure morphisms of the
members of a covering family of the final object of `(Sch/S)_fppf`; and
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage` — the effectivity half
of Stacks 023T, unconditional — says that datum is effective as soon as those structure morphisms
are an fpqc covering family of `S`.

**This file turns that effectivity into the local isomorphisms the gluing step consumes.**  An
effectivity witness is a quasi-coherent `𝒪_S`-module `𝓕` together with an isomorphism of its
canonical descent datum with the datum; its component at a member `X i` is an isomorphism

    `(objHom (X i))^* 𝓕 ≅ 𝓕_i`

downstairs, and Stacks 03DV in the functorial form
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` turns the left-hand side into
`𝓕^a|_{(Sch/X_i)_fppf}`, so composing with the given `𝓕_i^a ≅ 𝒢|_{(Sch/X_i)_fppf}` gives

    `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`,

which is exactly the input of
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_objRestrict` across the
bridge of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjRestrictRestrFunBridge.lean`.

What is **not** proved here is the *agreement* of those local isomorphisms over the fibre
products `X i ×_S X j`; see the implementation notes for exactly what it reduces to.

## Main definitions

* `Stacks.descentDataIsoComponent`: the component of an isomorphism of descent data for a
  pseudofunctor.
* `AlgebraicGeometry.BigFppfOver.effectiveGlueModule` and
  `AlgebraicGeometry.BigFppfOver.effectiveGlueComponentIso`: **the glued quasi-coherent module on
  `S` and the comparison of its pullback to a member with the local module there**, read off an
  effectivity witness of `AlgebraicGeometry.BigFppfOver.memberQcohDatum`.
* `AlgebraicGeometry.BigFppfOver.effectiveGlueObjRestrictIso`: **the local isomorphism
  `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`** of Stacks 03DX (1), in the `objRestrict`
  spelling.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_effectiveGlueModule`: the glued module is
  quasi-coherent, which is the property the witness of the essential image carries.
* `AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum`: **the datum of Stacks 03DX (1) is
  effective**, by the effectivity half of Stacks 023T, as soon as the structure morphisms of the
  members are an fpqc covering family of `S`.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree`: **the gluing step of
  Stacks 03DX (1) over the agreement of the local isomorphisms alone.**  Everything else — the
  datum, its effectivity, Stacks 03DV, Stacks 03EM and the bridge between the two spellings of
  the restriction — is discharged.

## Implementation notes

Nothing here carries a `stacks` attribute.  The declarations of this file still ask for the
agreement of the local isomorphisms over the fibre products; it is proved in the `objRestrict`
spelling in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreement.lean` and
transported into the spelling asked for here in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`,
where the clause is closed and the tag registered.  The other hypothesis,
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural`, is now the theorem
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural` and has been struck from every
declaration here and from the datum upstream.

**What the agreement reduces to.**  Write `q` for the structure morphism of `Z = X i ×_S X j`,
`g₁ : Z ⟶ X i` and `g₂ : Z ⟶ X j` for the two projections, `ι_i` for the component
`AlgebraicGeometry.BigFppfOver.effectiveGlueComponentIso` of the effectivity witness, and
`lac` for `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`.  Restricting
`AlgebraicGeometry.BigFppfOver.effectiveGlueObjRestrictIso` at `X i` to `Z` along `g₁` gives,
by naturality of `associatedModuleObjRestrictNatIso` in the module,

    `Λ_i⁻¹ ≫ (g₁^*ι_i)^a ≫ lac(g₁, 𝓕_i, e_i)`,

where `Λ_i` is `lac` at the ambient module `𝓕^a` of the local datum
`((objHom (X i))^*𝓕, associatedModuleObjRestrictNatIso.app 𝓕)`.  The descent condition
`CategoryTheory.Pseudofunctor.DescentData.Hom.comm` of the effectivity isomorphism, together with
`AlgebraicGeometry.BigFppfOver.memberDatum_hom_eq_transitionIso` and
`AlgebraicGeometry.BigFppfOver.associatedModule_map_transitionIso`, says precisely that

    `c_1^a ≫ (g₁^*ι_i)^a ≫ lac(g₁, 𝓕_i, e_i) = c_2^a ≫ (g₂^*ι_j)^a ≫ lac(g₂, 𝓕_j, e_j)`,

`c_k` being the comparisons `q^*𝓕 ≅ g_k^*(objHom (X i_k))^*𝓕` of
`AlgebraicGeometry.pullModComp`.  So the agreement is equivalent to

    `c_k^a ≫ Λ_{i_k} = associatedModuleObjRestrictNatIso.app 𝓕 at Z`,

that is, to the compatibility of the comparison of Stacks 03DV with composition of objects of the
big fppf site, read at the module `𝓕` and at the two projections, plus the transport of the
agreement across the bridge, for which `homRestr_app_eq` is the handle.

That compatibility is no longer an input.  It is exactly the component at `𝓕` of
`AlgebraicGeometry.BigFppfOver.NatIsoCompSquare` at the projection `g_k`, an identity between
natural isomorphisms of functors which mentions neither `𝒢` nor any local datum; and
`AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_sectionsCocycle` fed
`AlgebraicGeometry.BigFppfOver.sectionsCocycle` proves it at every base with no hypothesis.  The
earlier objection — that `AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` fixes the
ambient module, so reading the compatibility at `𝓕^a` rather than at `𝒢` was not literally
supplied — no longer bites either: `AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural`
holds for *every* sheaf of modules on `(Sch/S)_fppf`, so it may be instantiated at `𝓕^a`.

What therefore remains between this file and
`AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum` — and with it, by
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff`,
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` and the essential surjectivity
of Stacks 03DX (1) — is only the two unconditional reductions displayed above: the naturality
computation of the first display and the unfolding of
`CategoryTheory.Pseudofunctor.DescentData.Hom.comm` of the second.  Every lemma they consume
exists: `AlgebraicGeometry.BigFppfOver.memberDatum_hom_eq_transitionIso`,
`AlgebraicGeometry.BigFppfOver.associatedModule_map_transitionIso`, `homRestr_app_eq` and
`AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_sectionsCocycle`.  The consumer to discharge
is `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_of_forall_objRestrict`, whose
`hfpqc` is the very hypothesis
`AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum` asks for.

`AlgebraicGeometry.BigFppfOver.effectiveGlueComponentIso` is stated with
`AlgebraicGeometry.BigFppfOver.objHom` rather than with
`AlgebraicGeometry.BigFppfOver.memberStructureHom`, although the datum is a datum for the latter:
the two are the same morphism by one delta step, and the spelling with `objHom` is the one
`associatedModuleObjRestrictNatIso` uses, so no comparison is incurred when the two are composed.
The family of *schemes* is of course still the pinned one inside the datum — that is what
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlueDescentDatumViaUnprimed.lean`
measures — and nothing here unfolds it.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
-/

@[expose] public section

open CategoryTheory Opposite

universe t v' v u' u w

namespace Stacks

/-- **The component of an isomorphism of descent data.**  A morphism of descent data for a
pseudofunctor is a family of morphisms of the fibres satisfying a compatibility, and an
isomorphism of descent data therefore has an isomorphism of fibres at each index: the two
families of components of the isomorphism and of its inverse are inverse to each other, because
composition and the identity of `CategoryTheory.Pseudofunctor.DescentData` are componentwise. -/
public def descentDataIsoComponent {C : Type u} [Category.{v} C]
    {F : CategoryTheory.Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {D₁ D₂ : F.DescentData f} (Ψ : D₁ ≅ D₂) (i : ι) : D₁.obj i ≅ D₂.obj i where
  hom := Ψ.hom.hom i
  inv := Ψ.inv.hom i
  hom_inv_id := by
    rw [← CategoryTheory.Pseudofunctor.DescentData.comp_hom, Ψ.hom_inv_id,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]
  inv_hom_id := by
    rw [← CategoryTheory.Pseudofunctor.DescentData.comp_hom, Ψ.inv_hom_id,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]

end Stacks

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type w} (X : I → BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))
  (F : ∀ i, (objScheme B S hS (X i)).Modules) (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-! ### The datum is effective -/

/-- **The descent datum of Stacks 03DX (1) is effective.**  Its covering family is the family of
structure morphisms of the members, and as soon as that family is an fpqc covering family of `S`
the effectivity half of Stacks 023T — `AlgebraicGeometry.QuasicoherentDescentData`
`.isEffective_fpqcPrecoverage`, which carries no hypothesis — applies to it.

The fpqc hypothesis is stated on `AlgebraicGeometry.BigFppfOver.objHypercover`, the shape in
which `AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum` carries it; it is the same
hypothesis on the pinned family by
`AlgebraicGeometry.BigFppfOver.memberHypercover_presieve₀`. -/
public theorem isEffective_memberQcohDatum
    (hfpqc : (objHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) :
    (memberQcohDatum B S hS X G F hF e).IsEffective :=
  QuasicoherentDescentData.isEffective_fpqcPrecoverage (memberHypercover B S hS X)
    (by rw [memberHypercover_presieve₀]; exact hfpqc)
    (memberHypercoverQcohDatum B S hS X G F hF e)

/-! ### The glued module and the local isomorphisms -/

/-- **The quasi-coherent `𝒪_S`-module that the effectivity of the datum produces.**  Effectivity
is membership in the essential image of `AlgebraicGeometry.canonicalDescentFunctor`, so a witness
is a quasi-coherent module on `S` whose canonical descent datum is isomorphic to the datum; this
is that module.  It is the `𝓕` of the source's proof of Stacks 03DX (1). -/
public noncomputable def effectiveGlueModule
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) : S.Modules :=
  heff.witness.obj

/-- **The glued module is quasi-coherent**, the witness of the essential image being an object of
the full subcategory of quasi-coherent modules. -/
public theorem isQuasicoherent_effectiveGlueModule
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) :
    (effectiveGlueModule B S hS X G F hF e heff).IsQuasicoherent :=
  heff.witness.property

/-- **The isomorphism of descent data that effectivity supplies**, read after forgetting
quasi-coherence: the canonical descent datum of the glued module is isomorphic to the datum of
Stacks 03DX (1). -/
public noncomputable def effectiveGlueDatumIso
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) :
    ((canonicalDescentFunctor (memberStructureHom B S hS X)).obj heff.witness).obj ≅
      memberDatum B S hS X G F hF e :=
  (ObjectProperty.ι _).mapIso heff.getIso

/-- **The comparison of the pullback of the glued module with the local module at a member.**
The component at `i` of the isomorphism of descent data is an isomorphism

    `(objHom (X i))^* 𝓕 ≅ 𝓕_i`

of quasi-coherent modules on the scheme of `X i`: the component of the canonical datum of `𝓕` is
the pullback of `𝓕` along the structure morphism, and the component of the datum of
Stacks 03DX (1) is the local module `𝓕_i` itself by
`AlgebraicGeometry.BigFppfOver.memberQcohDatum_component`. -/
public noncomputable def effectiveGlueComponentIso
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) (i : I) :
    (Scheme.Modules.pullback (objHom B S hS (X i))).obj
        (effectiveGlueModule B S hS X G F hF e heff) ≅ F i :=
  Stacks.descentDataIsoComponent (effectiveGlueDatumIso B S hS X G F hF e heff) i

/-- **The local isomorphism of Stacks 03DX (1) in the `objRestrict` spelling.**

    `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`

for `𝓕` the glued module.  It is Stacks 03DV in its functorial form
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, which identifies the
restriction of `𝓕^a` to the big fppf site of the scheme of `X i` with the associated module of
the pullback of `𝓕` there, followed by the associated module of the comparison
`AlgebraicGeometry.BigFppfOver.effectiveGlueComponentIso` and by the given local isomorphism
`e i`. -/
public noncomputable def effectiveGlueObjRestrictIso
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) (i : I) :
    (objRestrict B S hS (X i)).obj
        ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)) ≅
      (objRestrict B S hS (X i)).obj G :=
  ((associatedModuleObjRestrictNatIso B S hS (X i)).app
      (effectiveGlueModule B S hS X G F hF e heff)).symm ≪≫
    (associatedModule B (objScheme B S hS (X i))
        (contains_objScheme B S hS (X i))).mapIso
      (effectiveGlueComponentIso B S hS X G F hF e heff i) ≪≫ e i

/-! ### The gluing step over the agreement alone -/

/-- **The gluing step of Stacks 03DX (1) over the agreement of the local isomorphisms alone.**  A
sheaf of modules `𝒢` on `(Sch/S)_fppf`, a family `X` of objects covering the final object whose
structure morphisms are an fpqc covering family of `S` and on whose members the restriction of
`𝒢` is the associated module of a quasi-coherent sheaf, exhibits `𝒢` in the essential image of
`𝓕 ↦ 𝓕^a` as soon as the local isomorphisms
`AlgebraicGeometry.BigFppfOver.effectiveGlueObjRestrictIso` agree over the fibre products
`X i ×_S X j`.

Everything else is discharged: the descent datum is
`AlgebraicGeometry.BigFppfOver.memberQcohDatum`, its effectivity is
`AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum` (the effectivity half of
Stacks 023T), the local isomorphisms are
`AlgebraicGeometry.BigFppfOver.effectiveGlueObjRestrictIso` (Stacks 03DV), the passage to the
relocalization spelling is `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso`, and the
assembly into a global isomorphism is
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_objRestrict`
(Stacks 03EM). -/
public theorem essImage_associatedModuleQcoh_of_agree
    (hX : (topology B S hS).CoversTop X)
    (hfpqc : (objHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (hagree : ∀ i j, homRestr (commStructurePresheaf B S hS)
          ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc))).val G.val
          (memberProdFst B S hS X i j)
          (objRestrictPreimageIso B S hS (effectiveGlueObjRestrictIso B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc) i)).hom.val =
        homRestr (commStructurePresheaf B S hS)
          ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc))).val G.val
          (memberProdSnd B S hS X i j)
          (objRestrictPreimageIso B S hS (effectiveGlueObjRestrictIso B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc) j)).hom.val) :
    (associatedModuleQcoh B S hS).essImage G :=
  let heff := isEffective_memberQcohDatum B S hS X G F hF e hfpqc
  essImage_associatedModuleQcoh_of_forall_objRestrict B S hS G X hX
    (effectiveGlueModule B S hS X G F hF e heff)
    (isQuasicoherent_effectiveGlueModule B S hS X G F hF e heff)
    (effectiveGlueObjRestrictIso B S hS X G F hF e heff) hagree

/-- **The gluing step of Stacks 03DX (1) over a single identity between module maps.**  This is
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` with its agreement
hypothesis read on sections through
`AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_eq_of_app`: all that is left of
Stacks 03DX (1)'s essential surjectivity is that for every object `W` of `(Sch/S)_fppf` over the
fibre product `X i ×_S X j` the component at `W` of the local isomorphism coming from `X i` is
the component at `W` of the one coming from `X j`.

Both components are maps between the *same* two modules — the sections of `𝓕^a` and of `𝒢` over
`W` — because the two objects of the slices at `X i` and at `X j` that `W` is read as have the
same underlying object of the site. -/
public theorem essImage_associatedModuleQcoh_of_agree_app
    (hX : (topology B S hS).CoversTop X)
    (hfpqc : (objHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (h : ∀ (i j : I) (A : (Over (memberProd B S hS X i j))ᵒᵖ),
      (objRestrictPreimageIso B S hS (effectiveGlueObjRestrictIso B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc) i)).hom.val.app
          (op ((Over.map (memberProdFst B S hS X i j)).obj A.unop)) =
        (objRestrictPreimageIso B S hS (effectiveGlueObjRestrictIso B S hS X G F hF e
            (isEffective_memberQcohDatum B S hS X G F hF e hfpqc) j)).hom.val.app
          (op ((Over.map (memberProdSnd B S hS X i j)).obj A.unop))) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModuleQcoh_of_agree B S hS X G F hF e hX hfpqc fun i j =>
    homRestr_objRestrictPreimageIso_eq_of_app B S hS (memberProdFst B S hS X i j)
      (memberProdSnd B S hS X i j) _ _ (h i j)

end AlgebraicGeometry.BigFppfOver

end
