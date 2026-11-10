module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LocallyQuasiCoherent

/-!
# Global surjectivity of the `f`-map on sections over an affine ambient scheme

Fix a global crystalline situation `(p, (S, I, γ), X)`, a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)` and a morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)`.
The proof of [Stacks, Tag 07JN] needs the **global** surjectivity of

`Γ(T', F_{T'}) ⟶ Γ(T, F_T)`

for an affine `T'` and `f` a closed immersion inside the subcategory `𝒞` of [Stacks, Tag 07JK].
This file proves it, from the two hypotheses of that proposition and nothing else.

The source's argument is: the `f`-map `F_{T'} ⟶ f_* F_T` is surjective as a map of sheaves (that
is hypothesis (2), in the form proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FMapSurjectivity.lean`), its kernel `K` is
quasi-coherent, and `H^1(T', K) = 0` because `T'` is affine; the long exact cohomology sequence
then makes `Γ(T', F_{T'}) ⟶ Γ(T', f_* F_T) = Γ(T, F_T)` surjective.  All four steps are carried
out below.

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`.

* `directImageModuleRestriction` — the direct image `f_* F_T`, read as a sheaf of `𝒪_{T'}`-modules
  on the ambient scheme `T'` of the target, namely as the scheme-theoretic pushforward of `F_T`
  along the map `T ⟶ T'` on ambient schemes.
* `fmapModuleRestriction` — **the `f`-map `F_{T'} ⟶ f_* F_T` as a morphism of sheaves of
  `𝒪_{T'}`-modules**, whose component over an open `W` of `T'` is the transition map
  `F(U' ∩ W, W, δ'|_W) ⟶ F(U ∩ f^{-1}W, f^{-1}W, δ|_{f^{-1}W})` of `F` itself.

## Main results

* `AlgebraicGeometry.morphismRestrict_appTop_topIso` — for a morphism of schemes `f : X ⟶ Y` and
  an open `U` of `Y`, the map on global sections of the restriction `f|_U : f^{-1}U ⟶ U` is
  `f^♯` over `U` under the identification of the global sections of an open subscheme with the
  sections over that open.  This is the compatibility that lets the crystalline `f`-map of the
  structure presheaf be read as the comorphism of a morphism of schemes.
* `...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply` — the same compatibility on the
  small crystalline site: the `f`-map of the structure presheaf of `Cris(X/S)` is the comorphism
  of the map `T ⟶ T'` on ambient schemes, under
  `...SmallSite.CrystallineThickening.sectionsIso`.
* `...isQuasicoherent_directImageModuleRestriction` — **`f_* F_T` is quasi-coherent** when `F` is
  locally quasi-coherent and `T ⟶ T'` is a closed immersion.  This is [Stacks, Tag 02KG] (a
  closed immersion is an affine morphism) applied to the restriction `F_T`, which is
  quasi-coherent by hypothesis (1).
* `...epi_fmapModuleRestriction` and `...epi_fmapModuleRestriction_of_isIso_toX` — the `f`-map is
  an epimorphism of sheaves of `𝒪_{T'}`-modules, by the local surjectivity of
  `FMapSurjectivity.lean`.
* `...isQuasicoherent_kernel_fmapModuleRestriction` — **the kernel `K` of the `f`-map is
  quasi-coherent**, being the kernel of a morphism of quasi-coherent modules.
* `...surjective_sections_fmapModuleRestriction` and
  `...surjective_sections_fmapModuleRestriction_of_isIso_toX` — **the global surjectivity of
  `Γ(T', F_{T'}) ⟶ Γ(T, F_T)` over an affine `T'`**, the second in the form
  [Stacks, Tag 07JN] uses it.

## What is and is not proved

`surjective_sections_fmapModuleRestriction_of_isIso_toX` is the step of [Stacks, Tag 07JN] in
full: its hypotheses
are exactly hypothesis (1) of that proposition
(`...SmallSite.IsLocallyQuasiCoherent`), hypothesis (2)
(`...CohomologyRestriction.IsSurjectiveComparison`), that the map `T ⟶ T'` on ambient schemes is
a closed immersion, that both objects lie over the whole of `X` — spelled out as `IsIso` of the
two structure maps, which is what cuts out the subcategory `𝒞` of [Stacks, Tag 07JK] — and that
`T'` is affine.  **No hypothesis stands in for a missing result**: in particular the
quasi-coherence of the kernel, which the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean` lists as available
and
which the writer of `FMapSurjectivity.lean` reported as absent, is *proved* here, as
`isQuasicoherent_kernel_fmapModuleRestriction`, from two results that were indeed already in the
library: `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`.

The affineness of `T'` is carried as the instance `[IsAffine T']` rather than deduced from
affineness of `X`; for an object over the whole of an affine `X` it is supplied by
`...SmallSite.isAffine_target_of_isAffine_source`, which this module does not import.

What this file does **not** do.

* It does not prove [Stacks, Tag 07JN].  The surjectivity proved here is one input of that
  proof, used there to make the transition maps of the inverse systems `e ↦ Γ(T_e, F)` of
  [Stacks, Tag 07JL] surjective; the remaining inputs are listed in the module documentation of
  `AffineCohomology.lean`.
* **No `@[stacks]` attribute is placed.**  This is a step inside the proof of
  [Stacks, Tag 07JN], not the content of a tag.

## Implementation notes

The direct image is taken to be the scheme-theoretic pushforward
`AlgebraicGeometry.Scheme.Modules.pushforward` along the map `T ⟶ T'` on ambient schemes, rather
than the pushforward of presheaves of modules along the `f`-map
`...CohomologyRestriction.restrictionFMap` of the structure presheaf.  The two have the same
underlying presheaf of abelian groups, but only the first carries the quasi-coherence of
[Stacks, Tag 02KG]; the price is that the `f`-map has to be checked to be semilinear over the
comorphism of the morphism of schemes rather than over `restrictionFMap`, and that is exactly
`sectionsIso_inv_restrictionFMap_apply`, whose scheme-theoretic content is
`AlgebraicGeometry.morphismRestrict_appTop_topIso_apply`.

**The surjectivity is stated for the component of `fmapModuleRestriction`, not for that of
`...CohomologyRestriction.moduleFMap`, and the two statements are not interchangeable.**  The two
maps have the same domain and codomain and are the same map of abelian groups, but they are maps
of modules over two different rings: the first over `Γ(T', ⊤)`, the second over the global
sections of the ambient scheme of the restriction of the object to `⊤`, which is
`Γ(T', ι ''ᵁ ⊤)`.  Those two rings are equal, not definitionally equal, so a statement about one
does not typecheck as a statement about the other; a consumer wanting the `moduleFMap` spelling
has to transport along that equality.  Nothing mathematical is hidden in this: the underlying
function is the transition map `F(U', T', δ') ⟶ F(U, T, δ)` of `F` in both readings, which is
what `fmapModuleRestriction` is built from.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

/-- **The map on global sections of the restriction of a morphism of schemes over an open of its
target is the comorphism over that open.**  For `f : X ⟶ Y` and `U` an open of `Y`, the square

`Γ(U, ⊤) ⟶ Γ(f^{-1}U, ⊤)`,  `Γ(Y, U) ⟶ Γ(X, f^{-1}U)`

commutes, the vertical identifications being `AlgebraicGeometry.Scheme.Opens.topIso`.

This is the inverse-image half of the statement that `f|_U` *is* `f` over `U`; it is obtained from
`AlgebraicGeometry.Scheme.Hom.resLE_app_top`, the restriction `f|_U` being
`f.resLE U (f^{-1}U) le_rfl`. -/
theorem morphismRestrict_appTop_topIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Scheme.Hom.appLE_eq_app]

/-- **`morphismRestrict_appTop_topIso` read on elements**, with the identifications on the other
side: a section of `𝒪_Y` over `U`, read as a global section of the open subscheme `U` and
transported by `f|_U`, is its image under `f^♯` over `U`, read as a global section of
`f^{-1}U`. -/
theorem morphismRestrict_appTop_topIso_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (r : Γ(Y, U)) :
    ((f ∣_ U).appTop).hom (U.topIso.inv.hom r) =
      ((f ⁻¹ᵁ U).topIso.inv).hom ((f.app U).hom r) := by
  have h : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← morphismRestrict_appTop_topIso f U,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom h r

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-! ### The `f`-map of the structure presheaf is the comorphism of a morphism of schemes -/

/-- **The `f`-map of the structure presheaf of `Cris(X/S)` is the comorphism of the map on
ambient schemes.**  Over an open `W` of the ambient scheme `T'` of the target, the `f`-map
`restrictionFMap` of the structure presheaf carries a section of `𝒪_{T'}` over `W` — read as a
section of the structure presheaf over the restriction of the target to `W` by
`SmallSite.CrystallineThickening.sectionsIso` — to the image of that section under the comorphism
`𝒪_{T'}(W) ⟶ 𝒪_T(f^{-1}W)` of the morphism of schemes `T ⟶ T'`, read likewise.

This is the semilinearity datum that lets the `f`-map of modules be read as a morphism into the
scheme-theoretic direct image.  Both sides are, by definition, maps of commutative rings attached
to schemes, and the statement about schemes is
`AlgebraicGeometry.morphismRestrict_appTop_topIso_apply` together with
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_targetHom`, which identifies
the restriction of `f` over `W` on ambient schemes with the restriction of a morphism of
schemes over an open. -/
theorem sectionsIso_inv_restrictionFMap_apply (W : B.obj.thickening.target.scheme.Opens)
    (r : (CrystallineThickening.ambientRingPresheaf B).obj (op W)) :
    ((restrictionFMap (crisRing S) g).app (op W)).hom
        ((CrystallineThickening.sectionsIso B W).inv.hom r) =
      (CrystallineThickening.sectionsIso A (g.hom.targetHom.hom ⁻¹ᵁ W)).inv.hom
        ((g.hom.targetHom.hom.app W).hom r) := by
  change ((Thickening.restrictOpenMap g.hom W).targetHom.hom.appTop).hom (W.topIso.inv.hom r) =
    ((g.hom.targetHom.hom ⁻¹ᵁ W).topIso.inv).hom ((g.hom.targetHom.hom.app W).hom r)
  rw [Thickening.restrictOpenMap_targetHom]
  exact morphismRestrict_appTop_topIso_apply _ _ _

/-! ### The direct image `f_* F_T` and the `f`-map into it -/

/-- **The direct image `f_* F_T` of the restriction of a sheaf of `𝒪_{X/S}`-modules, as a sheaf of
`𝒪_{T'}`-modules on the ambient scheme of the target.**  It is the scheme-theoretic pushforward of
the restriction `F_T` along the map `T ⟶ T'` on ambient schemes; its sections over an open `W` of
`T'` are therefore the sections of `F` over `(U ∩ f^{-1}W, f^{-1}W, δ|_{f^{-1}W})`. -/
def directImageModuleRestriction : B.obj.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward g.hom.targetHom.hom).obj
    (CrystallineThickening.moduleRestriction A F)

/-- **The `f`-map `F_{T'} ⟶ f_* F_T` as a morphism of sheaves of `𝒪_{T'}`-modules.**  Its
component over an open `W` of `T'` is the transition map of `F` along the restriction of `f` over
`W`, the same map as the component of
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleFMap`; what has to
be checked is that it is linear for the scalars of the structure sheaf of `T'`, which is
`sectionsIso_inv_restrictionFMap_apply`. -/
def fmapModuleRestriction :
    CrystallineThickening.moduleRestriction B F ⟶ directImageModuleRestriction F g :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (ringRestriction B)).map (moduleFMap F.val g))
    (fun W r m => by
      obtain ⟨W⟩ := W
      refine Eq.trans
        (((moduleFMap F.val g).app (op W)).hom.map_smul
          ((CrystallineThickening.sectionsIso B W).inv.hom r) m) ?_
      exact congrArg
        (fun s : (ringRestriction A).obj (op (g.hom.targetHom.hom ⁻¹ᵁ W)) =>
          s • id (α := ↥((moduleRestriction F.val A).obj (op (g.hom.targetHom.hom ⁻¹ᵁ W))))
            (((moduleFMap F.val g).app (op W)).hom m))
        (sectionsIso_inv_restrictionFMap_apply g W r))⟩

/-! ### Quasi-coherence of the direct image and of the kernel -/

/-- **The direct image `f_* F_T` of the restriction of a locally quasi-coherent sheaf of
`𝒪_{X/S}`-modules along a closed immersion is quasi-coherent.**  The restriction `F_T` is
quasi-coherent by hypothesis (1) of [Stacks, Tag 07JN]
(`...SmallSite.isQuasicoherent_moduleRestriction`), a closed immersion is an affine morphism, and
the direct image of a quasi-coherent module along an affine morphism is quasi-coherent, which is
[Stacks, Tag 02KG]. -/
theorem isQuasicoherent_directImageModuleRestriction (hF : IsLocallyQuasiCoherent F)
    (hg : IsClosedImmersion g.hom.targetHom.hom) :
    (directImageModuleRestriction F g).IsQuasicoherent :=
  have := hg
  have := isQuasicoherent_moduleRestriction hF A
  inferInstanceAs (((Scheme.Modules.pushforward g.hom.targetHom.hom).obj
    (CrystallineThickening.moduleRestriction A F)).IsQuasicoherent)

/-- **The `f`-map `F_{T'} ⟶ f_* F_T` is an epimorphism of sheaves of `𝒪_{T'}`-modules**, when
hypothesis (2) of [Stacks, Tag 07JN] holds, the map on ambient schemes is a closed immersion and
is surjective.  Epimorphisms of sheaves of modules are the locally surjective morphisms, and the
local surjectivity is `...CohomologyRestriction.isLocallySurjective_moduleFMap` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FMapSurjectivity.lean`. -/
theorem epi_fmapModuleRestriction (hM : IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base) :
    Epi (fmapModuleRestriction F g) := by
  apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
  have h := isLocallySurjective_moduleFMap F.val g hM hg hsurj
  constructor
  intro V s
  exact h.imageSieve_mem s

/-- **The `f`-map `F_{T'} ⟶ f_* F_T` is an epimorphism inside the subcategory `𝒞` of
[Stacks, Tag 07JK], with no extra hypothesis**: for a morphism between objects over the whole of
`X` whose map on ambient schemes is a closed immersion, hypothesis (2) of [Stacks, Tag 07JN]
suffices, the surjectivity on points being
`...CohomologyRestriction.surjective_targetHom_base_of_isIso_toX`. -/
theorem epi_fmapModuleRestriction_of_isIso_toX (hM : IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Epi (fmapModuleRestriction F g) :=
  epi_fmapModuleRestriction F g hM hg (surjective_targetHom_base_of_isIso_toX g hA hB)

/-- **The kernel `K` of the `f`-map `F_{T'} ⟶ f_* F_T` is quasi-coherent.**  Both `F_{T'}` and
`f_* F_T` are quasi-coherent — the first by hypothesis (1) of [Stacks, Tag 07JN], the second by
`isQuasicoherent_directImageModuleRestriction` — and the kernel of a morphism of quasi-coherent
modules on a scheme is quasi-coherent
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`).

This is the step of the source's proof that the record of this library disagreed about; see the
module documentation. -/
theorem isQuasicoherent_kernel_fmapModuleRestriction (hF : IsLocallyQuasiCoherent F)
    (hg : IsClosedImmersion g.hom.targetHom.hom) :
    (kernel (fmapModuleRestriction F g)).IsQuasicoherent :=
  have := isQuasicoherent_moduleRestriction hF B
  have := isQuasicoherent_directImageModuleRestriction F g hF hg
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (fmapModuleRestriction F g)

/-! ### Global surjectivity on sections -/

/-- **`Γ(T', F_{T'}) ⟶ Γ(T, F_T)` is surjective when `T'` is affine**, for a locally
quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed immersion comparison maps and a
morphism whose map on ambient schemes is a closed immersion and is surjective.  The map is the
component of the `f`-map `F_{T'} ⟶ f_* F_T` over the whole of `T'`, whose target is
`Γ(T', f_* F_T) = Γ(T, F_T)`.

The `f`-map is an epimorphism of sheaves of `𝒪_{T'}`-modules (`epi_fmapModuleRestriction`) with
quasi-coherent kernel `K` (`isQuasicoherent_kernel_fmapModuleRestriction`), so `H^1(T', K) = 0` by
[Stacks, Tag 01XB], and the long exact cohomology sequence of `0 ⟶ K ⟶ F_{T'} ⟶ f_* F_T ⟶ 0`
makes the map on global sections surjective. -/
theorem surjective_sections_fmapModuleRestriction (hF : IsLocallyQuasiCoherent F)
    (hM : IsSurjectiveComparison F.val) (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base)
    [IsAffine B.obj.thickening.target.scheme] :
    Function.Surjective ((fmapModuleRestriction F g).val.app (op ⊤)) := by
  have := epi_fmapModuleRestriction F g hM hg hsurj
  have := isQuasicoherent_kernel_fmapModuleRestriction F g hF hg
  have hS : (ShortComplex.mk (kernel.ι (fmapModuleRestriction F g)) (fmapModuleRestriction F g)
      (kernel.condition (fmapModuleRestriction F g))).ShortExact :=
    { exact := ShortComplex.exact_kernel (fmapModuleRestriction F g) }
  exact Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one
    B.obj.thickening.target.scheme ⊤ hS
    (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine _
      (kernel (fmapModuleRestriction F g)) 1 one_pos)

/-- **`Γ(T', F_{T'}) ⟶ Γ(T, F_T)` is surjective for an affine `T'` and a closed immersion inside
the subcategory `𝒞` of [Stacks, Tag 07JK], assuming only the two hypotheses of
[Stacks, Tag 07JN].**  This is the form in which the proof of that proposition uses the
surjectivity: the objects of its category `𝒞` are those over the whole of `X`, that is, those
with `IsIso A.obj.toX`, and for a morphism between two of them the surjectivity on points that
`surjective_sections_fmapModuleRestriction` asks for is automatic. -/
theorem surjective_sections_fmapModuleRestriction_of_isIso_toX (hF : IsLocallyQuasiCoherent F)
    (hM : IsSurjectiveComparison F.val) (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX)
    [IsAffine B.obj.thickening.target.scheme] :
    Function.Surjective ((fmapModuleRestriction F g).val.app (op ⊤)) :=
  surjective_sections_fmapModuleRestriction F g hF hM hg
    (surjective_targetHom_base_of_isIso_toX g hA hB)

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

end

end
