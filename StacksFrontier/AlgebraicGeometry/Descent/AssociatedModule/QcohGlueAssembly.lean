module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfInternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Assembling the local associated modules of Stacks 03DX (1) into a global one

The gluing step of Stacks 03DX (1), `AlgebraicGeometry.BigFppfOver`
`.EssImageAssociatedModuleQcohGlue`, has three inputs in the source: full faithfulness of
`𝓕 ↦ 𝓕^a` (Stacks 0GN7), the effectivity of descent for quasi-coherent sheaves (Stacks 023T),
and the sheaf property of `SheafHom(𝓕^a, 𝒢)` (Stacks 03EM).  This file carries out the **third**
of them — the assembly of a family of local isomorphisms into a global one — and reduces the
gluing step to the first two.

The assembly is `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_isCompatible`:
a quasi-coherent `𝓕` on `S` together with a compatible family of isomorphisms
`𝓕^a|_{X i} ≅ 𝒢|_{X i}` on a family covering the final object of `(Sch/S)_fppf` exhibits `𝒢` in
the essential image.  Compatibility is Mathlib's
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`, which quantifies over every
object of the site mapping into two members of the family; the source instead checks the
agreement of the local isomorphisms over the fibre products `X i ×_S X j`, and
`AlgebraicGeometry.BigFppfOver.isCompatible_of_forall_memberProd` is the (purely formal) step
from the second to the first, the relocalization maps of the internal hom being functorial.

What is **not** done here is the descent datum: the construction, out of a module on
`(Sch/S)_fppf` whose restriction to each member of a covering family of the final object is an
associated module, of an fpqc covering family of `S` downstairs and a quasi-coherent descent
datum for it whose effectivity returns the glued `𝓕` with its local isomorphisms.  That is
isolated as `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` and is the only
residue: see the implementation notes for what it would take.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.memberProd`: the fibre product `X i ×_S X j` of two members of
  a family of objects of `(Sch/S)_fppf`, formed as a pullback over the final object.
* `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum`: **the descent datum of
  Stacks 03DX (1)** as a hypothesis — out of the local associated-module data on a covering
  family of the final object, an fpqc covering family of `S` and a quasi-coherent descent datum
  for it whose effectivity (Stacks 023T) yields a quasi-coherent `𝓕` on `S` and local
  isomorphisms `𝓕^a|_{X i} ≅ 𝒢|_{X i}` agreeing over the `X i ×_S X j`.

## Main results

* `homRestr_restrFun_map`: relocalizing the restriction of a global morphism returns its
  restriction — the statement that those restrictions are a section of the internal hom.
* `AlgebraicGeometry.BigFppfOver.isCompatible_of_forall_memberProd`: a family of local morphisms
  agreeing over the fibre products `X i ×_S X j` is a compatible family.
* `AlgebraicGeometry.BigFppfOver.isCompatible_restrFun_map`: the restrictions of a global
  morphism are a compatible family, for every family of objects.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_isCompatible` and
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd`: **the
  Stacks 03EM step of Stacks 03DX (1)**, unconditionally — a quasi-coherent `𝓕` on `S` with
  local isomorphisms `𝓕^a|_{X i} ≅ 𝒢|_{X i}` agreeing over the fibre products exhibits `𝒢` in
  the essential image of `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.BigFppfOver.isIso_of_forall_isIso_restrFun`: a morphism of sheaves of
  modules on `(Sch/S)_fppf` whose restrictions to the members of a covering family of the final
  object are isomorphisms is an isomorphism.  Unconditional, and the form in which a *global*
  comparison morphism may be checked locally.
* `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohGlue_of_isEffective`: **the gluing
  step of Stacks 03DX (1) over the effectivity half of Stacks 023T and the descent datum.**
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_isEffective` and
  `AlgebraicGeometry.BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_isEffective`:
  **Stacks 03DX (1), essential surjectivity**, at `S` and over every base of the site, over the
  same two inputs.  The second is the shape in which
  `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`
  consumes it.
* `AlgebraicGeometry.BigFppfOver.associatedModuleGlueDescentDatum_of_quasicoherentIsEssImage`:
  the residue is *implied* by the conclusion it is used for, so it is not a strengthening of
  Stacks 03DX (1)'s essential surjectivity.

## Implementation notes

Nothing here carries a `stacks` attribute: every statement about a clause of Stacks 03DX is
still conditional on the two inputs, and a hypothesis is part of a citation.

The effectivity hypothesis is spelled out rather than imported under a name, as

```
∀ {T : Scheme.{u}} (𝒰 : PreZeroHypercover.{u + 1} T),
  𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T → ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective
```

which is the right-hand side of
`AlgebraicGeometry.QuasicoherentDescentData.effectiveGluesOverAffineOpens_iff` at index universe
`u + 1`; `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_of_glues`
discharges it at every index universe, so no restatement is needed when the effectivity half of
Stacks 023T lands.  The index universe is forced to be `u + 1`: the covering families of the
final object of `(Sch/S)_fppf` that Stacks 03DN produces are indexed by the objects of that
site, which form a `Type (u + 1)`.

The local isomorphisms are stated with the relocalization functor `restrFun` of the internal hom
rather than with `SheafOfModules.overFunctor`, because that is the shape in which
`AlgebraicGeometry.BigFppfOver.exists_iso_of_isCompatible` — the 03EM input — consumes and
returns them, so no comparison of the two spellings of `𝓕^a|_{X i}` is incurred.

What the residue needs, and why it is not supplied here: the library compares the big fppf site
of `S` with the schemes over `S` only at one object at a time, by
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` (Stacks 03DV), and has no functor from
modules on `(Sch/S)_fppf` together with a covering family to `AlgebraicGeometry`
`.QuasicoherentDescentData` — no statement in the library mentions both.  Two further pieces are
missing for it.  A family `X : I → BigFppfOver B S hS` with
`(topology B S hS).CoversTop X` is *not* an fpqc covering family of `S`: the objects of the big
fppf category over `S` are arbitrary schemes over `S`, so the structure morphisms need not even
be flat, and only a refinement of the generated covering sieve — `AlgebraicGeometry.BigFppfSite`
`.exists_isCovering_sieve₀_le` — is an fppf, hence fpqc, covering family; transporting the local
data along the factorizations is base change along morphisms of the big site, which is where the
object-wise Stacks 03DV comparison has to be made functorial.  And the transition isomorphisms
of the datum come from full faithfulness of `𝓕 ↦ 𝓕^a` over `X i ×_S X j`
(`AlgebraicGeometry.BigFppfOver.full_associatedModuleQcoh_of_fpqcDescent` and
`…faithful_associatedModuleQcoh_of_fpqcDescent`, both unconditional once fed
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`), their cocycle condition from faithfulness
over the triple products — again through the same missing functoriality.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

section InternalHom

variable {C : Type*} [Category C] (O : Cᵒᵖ ⥤ CommRingCat)
  (F G : PresheafOfModules.{w} (Oforget O))

/-- **Relocalizing the restriction of a global morphism returns its restriction.**  The
restrictions `F|_U ⟶ G|_U` of a morphism `F ⟶ G` form a *section* of the internal hom, which is
exactly this compatibility with the relocalization maps. -/
public theorem homRestr_restrFun_map {V U : C} (f : V ⟶ U) (ψ : F ⟶ G) :
    homRestr O F G f ((restrFun O U).map ψ) = (restrFun O V).map ψ := rfl

end InternalHom

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Compatibility checked on fibre products -/

/-- **The fibre product `X i ×_S X j` of two members of a family of objects of
`(Sch/S)_fppf`.**  It is the pullback of the two morphisms to the final object `S` over itself,
which exists because the big fppf category over `S` has pullbacks. -/
public noncomputable abbrev memberProd {I : Type w} (X : I → BigFppfOver B S hS) (i j : I) :
    BigFppfOver B S hS :=
  pullback (Over.mkIdTerminal.from (X i)) (Over.mkIdTerminal.from (X j))

/-- The first projection `X i ×_S X j ⟶ X i`. -/
public noncomputable abbrev memberProdFst {I : Type w} (X : I → BigFppfOver B S hS) (i j : I) :
    memberProd B S hS X i j ⟶ X i :=
  pullback.fst _ _

/-- The second projection `X i ×_S X j ⟶ X j`. -/
public noncomputable abbrev memberProdSnd {I : Type w} (X : I → BigFppfOver B S hS) (i j : I) :
    memberProd B S hS X i j ⟶ X j :=
  pullback.snd _ _

/-- **Every pair of morphisms into two members of the family factors through their fibre
product**, `X i ×_S X j` being a fibre product over the final object and the two composites into
the final object agreeing for that reason alone. -/
public theorem exists_hom_memberProd {I : Type w} (X : I → BigFppfOver B S hS)
    {Z : BigFppfOver B S hS} {i j : I} (f : Z ⟶ X i) (g : Z ⟶ X j) :
    ∃ m : Z ⟶ memberProd B S hS X i j,
      f = m ≫ memberProdFst B S hS X i j ∧ g = m ≫ memberProdSnd B S hS X i j :=
  ⟨pullback.lift f g (Over.mkIdTerminal.hom_ext _ _),
    (pullback.lift_fst f g (Over.mkIdTerminal.hom_ext _ _)).symm,
    (pullback.lift_snd f g (Over.mkIdTerminal.hom_ext _ _)).symm⟩

/-- **The agreement of a family of local morphisms over the fibre products `X i ×_S X j` is
compatibility.**  Mathlib's `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`
quantifies over an arbitrary object mapping into two members of the family, whereas the source
of Stacks 03DX (1) checks the agreement only over the fibre products; the two are the same
condition because every such pair of morphisms factors through the fibre product by
`AlgebraicGeometry.BigFppfOver.exists_hom_memberProd`, and relocalization of internal-hom
sections is functorial by `homRestr_comp`. -/
public theorem isCompatible_of_forall_memberProd
    (F G : PresheafOfModules.{u} (Oforget (commStructurePresheaf B S hS))) {I : Type w}
    (X : I → BigFppfOver B S hS)
    (α : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj F ⟶
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G)
    (hα : ∀ i j, homRestr (commStructurePresheaf B S hS) F G
          (memberProdFst B S hS X i j) (α i) =
        homRestr (commStructurePresheaf B S hS) F G (memberProdSnd B S hS X i j) (α j)) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (commStructurePresheaf B S hS) F G).presheaf ⋙
        CategoryTheory.forget _) α := by
  intro Z i j f g
  obtain ⟨m, hf, hg⟩ := exists_hom_memberProd B S hS X f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply, hf, hg, homRestr_comp,
    homRestr_comp, hα i j]

/-- **The restrictions of a global morphism are a compatible family.**  Relocalizing the
restriction `F|_U ⟶ G|_U` of a morphism `F ⟶ G` returns its restriction, by
`homRestr_restrFun_map`, so the compatibility condition holds with no hypothesis on the family
of objects at all. -/
public theorem isCompatible_restrFun_map
    (F G : PresheafOfModules.{u} (Oforget (commStructurePresheaf B S hS))) {I : Type w}
    (X : I → BigFppfOver B S hS) (ψ : F ⟶ G) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (commStructurePresheaf B S hS) F G).presheaf ⋙
        CategoryTheory.forget _)
      (fun i => (restrFun (commStructurePresheaf B S hS) (X i)).map ψ) := by
  intro Z i j f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply, homRestr_restrFun_map,
    homRestr_restrFun_map]

/-! ### The Stacks 03EM step: assembling the local isomorphisms -/

/-- **The Stacks 03EM step of Stacks 03DX (1)**, unconditionally.  A quasi-coherent
`𝒪_S`-module `𝓕` together with a *compatible* family of isomorphisms `𝓕^a|_{X i} ≅ 𝒢|_{X i}` on
a family of objects covering the final object of `(Sch/S)_fppf` exhibits `𝒢` in the essential
image of the functor `𝓕 ↦ 𝓕^a` of Stacks 06VE.

This is the sentence "the sheaf property of `SheafHom(𝓕^a, 𝒢)` assembles the local isomorphisms
into a global one" of the source's proof: the gluing is
`AlgebraicGeometry.BigFppfOver.exists_iso_of_isCompatible`, which is Stacks 03EM at the big fppf
site and carries no hypothesis. -/
public theorem essImage_associatedModuleQcoh_of_isCompatible
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type w}
    {X : I → BigFppfOver B S hS} (hX : (topology B S hS).CoversTop X) (𝓕 : S.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj
        ((associatedModule B S hS).obj 𝓕).val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS ((associatedModule B S hS).obj 𝓕).val G.val).presheaf ⋙
        CategoryTheory.forget _) (fun i => (e i).hom)) :
    (associatedModuleQcoh B S hS).essImage G := by
  obtain ⟨φ, -⟩ :=
    exists_iso_of_isCompatible B S hS ((associatedModule B S hS).obj 𝓕) G hX e he
  exact ⟨⟨𝓕, h𝓕⟩, ⟨φ⟩⟩

/-- **The Stacks 03EM step of Stacks 03DX (1), with compatibility checked where the source
checks it**, unconditionally: over the fibre products `X i ×_S X j`. -/
public theorem essImage_associatedModuleQcoh_of_forall_memberProd
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type w}
    (X : I → BigFppfOver B S hS) (hX : (topology B S hS).CoversTop X) (𝓕 : S.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj
        ((associatedModule B S hS).obj 𝓕).val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : ∀ i j, homRestr (commStructurePresheaf B S hS)
          ((associatedModule B S hS).obj 𝓕).val G.val
          (memberProdFst B S hS X i j) (e i).hom =
        homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
          (memberProdSnd B S hS X i j) (e j).hom) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModuleQcoh_of_isCompatible B S hS G hX 𝓕 h𝓕 e
    (isCompatible_of_forall_memberProd B S hS _ _ X _ he)

/-- **Being an isomorphism is local on a covering family of the final object of
`(Sch/S)_fppf`.**  A morphism of sheaves of modules whose restriction to each member of a family
covering the final object is an isomorphism is itself an isomorphism.

The restrictions of a global morphism are automatically a compatible family
(`homRestr_restrFun_map`), so Stacks 03EM glues them to an isomorphism `F ≅ G`; the uniqueness
clause of the gluing then identifies that isomorphism's underlying morphism with the given
one. -/
public theorem isIso_of_forall_isIso_restrFun
    {F G : SheafOfModules.{u} (structureSheaf B S hS)} (φ : F ⟶ G) {I : Type w}
    {X : I → BigFppfOver B S hS} (hX : (topology B S hS).CoversTop X)
    (h : ∀ i, IsIso ((restrFun (commStructurePresheaf B S hS) (X i)).map φ.val)) :
    IsIso φ := by
  have hcomp : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS F.val G.val).presheaf ⋙ CategoryTheory.forget _)
      (fun i => (restrFun (commStructurePresheaf B S hS) (X i)).map φ.val) :=
    isCompatible_restrFun_map B S hS _ _ X φ.val
  obtain ⟨ψ, hψ⟩ := exists_iso_of_isCompatible B S hS F G hX
    (fun i => asIso ((restrFun (commStructurePresheaf B S hS) (X i)).map φ.val)) hcomp
  obtain ⟨χ, -, hu⟩ := existsUnique_hom_of_isCompatible B S hS F.val G hX hcomp
  have hval : φ.val = ψ.hom.val := (hu _ fun _ => rfl).trans (hu _ hψ).symm
  rw [SheafOfModules.Hom.ext hval]
  infer_instance

/-! ### The residue: the descent datum -/

/-- **The descent datum of Stacks 03DX (1)** as a hypothesis.  Out of a sheaf of modules `𝒢` on
`(Sch/S)_fppf` whose restriction to the big fppf site of the scheme of each member of a covering
family `X` of the final object is the associated module of a quasi-coherent sheaf there, it
produces an fpqc covering family of `S` downstairs and a quasi-coherent descent datum for it
whose effectivity — the effectivity half of Stacks 023T — returns a quasi-coherent `𝒪_S`-module
`𝓕` together with isomorphisms `𝓕^a|_{X i} ≅ 𝒢|_{X i}` agreeing over the fibre products
`X i ×_S X j`.

This is the first two paragraphs of the source's proof after the local step: full faithfulness
of `𝓕 ↦ 𝓕^a` (Stacks 0GN7, unconditional here) turning the canonical isomorphisms of `𝒢` over
`X i ×_S X j` into a descent datum on the `𝓕_i`, and the gluing of that datum.  The assembly of
the local isomorphisms into a global one — the Stacks 03EM paragraph — is *not* part of it: that
is `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd` and is
proved. -/
public abbrev AssociatedModuleGlueDescentDatum : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (I : Type (u + 1))
      (X : I → BigFppfOver B S hS), (topology B S hS).CoversTop X →
      (∀ i, ∃ F : (objScheme B S hS (X i)).Modules, F.IsQuasicoherent ∧
        Nonempty ((associatedModule B (objScheme B S hS (X i))
          (contains_objScheme B S hS (X i))).obj F ≅ (objRestrict B S hS (X i)).obj G)) →
    ∃ (𝒰 : PreZeroHypercover.{u + 1} S) (_ : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
      (D : QuasicoherentDescentData 𝒰.f), D.IsEffective →
        ∃ (𝓕 : S.Modules) (_ : 𝓕.IsQuasicoherent)
          (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj
              ((associatedModule B S hS).obj 𝓕).val ≅
            (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val),
          ∀ i j, homRestr (commStructurePresheaf B S hS)
                ((associatedModule B S hS).obj 𝓕).val G.val
                (memberProdFst B S hS X i j) (e i).hom =
            homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
              (memberProdSnd B S hS X i j) (e j).hom

/-- **The gluing step of Stacks 03DX (1) for `τ = fppf`, over the effectivity half of
Stacks 023T and the descent datum.**  A sheaf of modules on `(Sch/S)_fppf` whose restriction to
the big fppf site of the scheme of each member of a covering family of the final object is the
associated module of a quasi-coherent sheaf there is itself an `𝓕^a`.

The Stacks 03EM input is discharged by
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd`, and the
effectivity hypothesis `hEff` is applied to the family and the datum that `hD` produces. -/
public theorem essImageAssociatedModuleQcohGlue_of_isEffective
    (hEff : ∀ {T : Scheme.{u}} (𝒰 : PreZeroHypercover.{u + 1} T),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T →
        ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective)
    (hD : AssociatedModuleGlueDescentDatum B S hS) :
    EssImageAssociatedModuleQcohGlue B S hS := by
  intro G I X hX hF
  obtain ⟨𝒰, h𝒰, D, hglue⟩ := hD G I X hX hF
  obtain ⟨𝓕, h𝓕, e, he⟩ := hglue (hEff 𝒰 h𝒰 D)
  exact essImage_associatedModuleQcoh_of_forall_memberProd B S hS G X hX 𝓕 h𝓕 e he

/-- **Stacks 03DX (1), essential surjectivity, for `τ = fppf`, over the effectivity half of
Stacks 023T and the descent datum.**  Every quasi-coherent `𝒪`-module on the big fppf site of
`S` is isomorphic to `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`.

The globalization of the gluing step is
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_glue`, which is
unconditional. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_isEffective
    (hEff : ∀ {T : Scheme.{u}} (𝒰 : PreZeroHypercover.{u + 1} T),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T →
        ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective)
    (hD : AssociatedModuleGlueDescentDatum B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_glue B S hS
    (essImageAssociatedModuleQcohGlue_of_isEffective B S hS hEff hD)

/-- **Stacks 03DX (1), essential surjectivity, over every base of the big fppf site**, over the
effectivity half of Stacks 023T and the descent datum at each base.  This is the shape in which
`AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`
consumes essential surjectivity: its hypothesis quantifies over every scheme of the site, not
only over `S`. -/
public theorem forall_quasicoherentIsEssImageAssociatedModule_of_isEffective
    (hEff : ∀ {T : Scheme.{u}} (𝒰 : PreZeroHypercover.{u + 1} T),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T →
        ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective)
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T), AssociatedModuleGlueDescentDatum B T hT) :
    ∀ (T : Scheme.{u}) (hT : B.Contains T), QuasicoherentIsEssImageAssociatedModule B T hT :=
  fun T hT => quasicoherentIsEssImageAssociatedModule_of_isEffective B T hT hEff (hD T hT)

/-- **The residue is implied by the conclusion it is used for**, so assuming it is not a
strengthening of Stacks 03DX (1)'s essential surjectivity.  Given a global isomorphism
`𝓕^a ≅ 𝒢`, take for the fpqc covering family the one-element family `{𝟙 S}` and for the datum
the canonical datum of `𝓕`, which is effective by definition; the local isomorphisms are the
restrictions of the global one and they agree over the fibre products because relocalizing the
restriction of a global morphism returns its restriction. -/
public theorem associatedModuleGlueDescentDatum_of_quasicoherentIsEssImage
    (h : QuasicoherentIsEssImageAssociatedModule B S hS) :
    AssociatedModuleGlueDescentDatum B S hS := by
  intro G I X hX hF
  obtain ⟨⟨𝓕, h𝓕⟩, ⟨φ⟩⟩ := essImageAssociatedModuleQcohGlue_of_quasicoherentIsEssImage
    B S hS h G I X hX hF
  refine ⟨PreZeroHypercover.singleton.{u + 1} (𝟙 S), ?_,
    (canonicalDescentFunctor _).obj ⟨𝓕, h𝓕⟩, fun _ => ?_⟩
  · rw [PreZeroHypercover.presieve₀_singleton]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage (𝟙 S)
  · refine ⟨𝓕, h𝓕, fun i => (restrFun (commStructurePresheaf B S hS) (X i)).mapIso
      ((SheafOfModules.forget _).mapIso φ), fun i j => ?_⟩
    rfl

end BigFppfOver

end AlgebraicGeometry

end
