module

public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.Comparison
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk

/-!
# The stalk of a locally free sheaf of modules on a scheme is free

Mathlib records local freeness of a sheaf of modules through
`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`, on the slice site, and says nothing
about stalks: `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` compares the stalk of a
module with the stalk of its restriction to an open set **only as abelian groups**, with no
semilinearity statement, and there is no identification of the stalk of `SheafOfModules.free I`
with a free module over the stalk of the sheaf of rings.

This file supplies the missing semilinear comparison in the `LocalGeneratorsData` vocabulary.
The mathematics is Stacks Tag 01C9's, already formalized in this repository in its own
`LocallyFreeRank.Trivialization` vocabulary; what is added is the identification of the two
vocabularies (`StalkFreeBridge.Comparison`) and the consequences for a scheme that the slice-site
predicates can actually consume.

## Main results

* `Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv`: generating sections of `M.over U` whose
  structure map is an isomorphism give, at every point `x ∈ U`, an `𝒪_{X,x}`-linear equivalence
  `M_x ≃ₗ (G.I →₀ 𝒪_{X,x})`. This is the semilinear stalk comparison.
* `Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv_of_isLocallyFreeData` is the same statement
  for the `i`-th member of locally free local generators data, and
  `Stacks.StalkFreeBridge.nonempty_stalkBasis_of_isLocallyFreeData` phrases it as a basis of the
  stalk indexed by `(q.generators i).I`.
* `Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree`: the stalk of a locally free sheaf of
  modules on a scheme is a free module over the local ring at that point. This is the
  implication (3) ⟹ (2)-at-stalks of Stacks Tag 05P2, free of finiteness hypotheses.
* `Stacks.StalkFreeBridge.finite_index_of_isLocallyFreeData`: if the stalk at a point of a member
  of locally free local generators data is a *finite* module, that member's index type is finite.
  This is the rank-finiteness step of the implication (3) ⟹ (4) of Tag 05P2, which the file
  `StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean` records as blocked: it is the
  "shrinking argument run at the stalk".
* `Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`: the stalk of a finite
  locally free sheaf is a finite free module over the local ring.
* `Stacks.StalkFreeBridge.isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk` is the whole of
  the implication (3) ⟹ (4) of Tag 05P2 except one step: a locally free sheaf of modules on a
  scheme whose every stalk is a finite module is finite locally free. The step not supplied is
  "a sheaf of modules of finite type has finitely generated stalks", which is what entry (3)'s
  `IsFiniteType` is for; see the implementation notes.

## Implementation notes

**Which `IsFiniteLocallyFree` is consumed.** The repository carries two classes with
character-identical bodies: `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`
(`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`), tagged `@[stacks 01C6 "(2)"]`, and
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`
(`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean`), untagged. The results here are
stated over the first: it is in a library namespace, it is the one carrying the Stacks attribute
for Tag 01C6, and it is therefore the canonical realization. Since the Tag 05P2
consequences already proved — local freeness, finite type, finite presentation — hang off the
second, `Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree` crosses from the tagged
class to it, so that nothing here needs a third copy. That bridge is a one-liner precisely
because the two classes say the same thing; they should be deduplicated.

**What Tag 05P2 still needs.** The one step missing from
`isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk` is: for `M : X.Modules` with
`M.IsFiniteType`, every stalk `M_x` is a finite `𝒪_{X,x}`-module. The route is available but was
not walked here: `Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiLocallySurjective.lean`) turns the epimorphism
`(σ.generators j).π` into local surjectivity, and
`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` turns that into surjectivity on
stalks; what is then needed is the same slice-site-to-open-subspace transport as in
`StalkFreeBridge.Comparison`, but for generating sections whose structure map is only an
epimorphism, composed with Tag 01C9's `stalk_restrictMod_linearEquiv` and
`stalk_free_linearEquiv` to read the surjection as a surjection `((σ.generators j).I →₀ k) → M_x`
of modules over the *restricted* ring stalk `k`, and finally transported along Tag 01C9's
`restrictStalkRingEquiv`. That is the semilinear bookkeeping of this file done once more for a
non-invertible map.

The implication (1) ⟹ (4) needs the same step and one more thing. Entry (1) — flatness together
with finite presentation — *is* expressible at sheaf level in this repository, as
`AlgebraicGeometry.SheafOfModules.IsFlat` (`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`),
and its stalkwise half is already proved: `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`
(Tag 05NE) yields `Module.Flat` of the stalk in exactly the spelling used here. The spreading step
is present too, as `Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis` (Tag 0B8J). The
first of the two steps that were missing here, `Module.FinitePresentation` of the stalk from
`M.IsFinitePresentation`, is now `Stacks.StalkFiniteType.finitePresentation_stalk`
(`StacksFrontier/AlgebraicGeometry/StalkFiniteType/FinitePresentation.lean`), proved affine-locally
through the tilde construction rather than by the transport sketched above. What remains is the
second, a mismatch at the base ring: Tag 0B8J states its hypothesis over
the `RingCat`-valued stalk `TopCat.Presheaf.stalk X.ringCatSheaf.obj x`, whereas this file and Tag
01C9 work over the `CommRingCat`-valued stalk `X.presheaf.stalk x`. Those are two filtered
colimits taken in different categories and they do not meet. The comparison is
`preservesColimitIso (forget₂ CommRingCat RingCat)`, which Tag 01C9 builds twice — inside
`Trivialization.stalk_restrictRing_ringEquiv` and inside `restrictStalkRingEquiv` — without ever
exposing it as a declaration. Exposing it, and transporting a `Module.Basis` along it, is what
would let the output of this file drive Tag 0B8J.

**The module structure on the stalk.** `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` gives
`Module (R.stalk x) (stalk M.presheaf x)` for a presheaf of modules over a presheaf of
*commutative* rings `R`, but instance search does not fire through the `sheafCompose`-wrapper by
which `X.ringCatSheaf` is built from `X.sheaf`. Tag 01C9 names that instance for its own
spelling (`LocallyFreeRank.instModuleStalkF`); `AlgebraicGeometry.Scheme.Modules.moduleStalk`
names it at the `AlgebraicGeometry.Scheme.Modules` spelling, which is the one a consumer on a
scheme has.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe w u

namespace Stacks.StalkFreeBridge

variable {X : Scheme.{u}}

/-- Every point of the space lies in some member of an open covering family. -/
private theorem exists_mem_of_coversTop {T : Type u} [TopologicalSpace T] {ι : Type w}
    (U : ι → Opens T) (hU : (Opens.grothendieckTopology T).CoversTop U) (x : T) :
    ∃ i, x ∈ U i :=
  ((Opens.coversTop_iff T U).1 hU).exists_mem x

/-- **The semilinear stalk comparison.** A family of generating sections of `M.over U` whose
structure map `free G.I ⟶ M.over U` is an isomorphism exhibits, at every point `x` of `U`, the
stalk `M_x` as the free `𝒪_{X,x}`-module on `G.I`.

This is the statement Mathlib lacks: its `Scheme.Modules.restrictStalkNatIso` compares the two
stalks only as abelian groups. The proof is Stacks Tag 01C9's
`LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp`, reached through
`Stacks.StalkFreeBridge.trivializationOfGeneratingSections`. -/
theorem nonempty_stalkLinearEquiv (U : X.Opens) (M : X.Modules)
    (G : (M.over U).GeneratingSections) [IsIso G.π] {x : X} (hx : x ∈ U) :
    Nonempty (ToType (TopCat.Presheaf.stalk M.val.presheaf x)
      ≃ₗ[ToType (X.presheaf.stalk x)] (G.I →₀ ToType (X.presheaf.stalk x))) :=
  LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp (X : TopCat.{u}) X.sheaf M x hx
    (trivializationOfGeneratingSections U M G)

/-- The semilinear stalk comparison for the `i`-th member of locally free local generators data:
at a point of `q.X i`, the stalk of `M` is the free `𝒪_{X,x}`-module on `(q.generators i).I`. -/
theorem nonempty_stalkLinearEquiv_of_isLocallyFreeData (M : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [hq : q.IsLocallyFreeData] (i : q.I)
    {x : X} (hx : x ∈ q.X i) :
    Nonempty (ToType (TopCat.Presheaf.stalk M.val.presheaf x)
      ≃ₗ[ToType (X.presheaf.stalk x)] ((q.generators i).I →₀ ToType (X.presheaf.stalk x))) :=
  have := hq.isIso i
  nonempty_stalkLinearEquiv (q.X i) M (q.generators i) hx

/-- The same, read as a basis of the stalk indexed by the local generators. -/
theorem nonempty_stalkBasis_of_isLocallyFreeData (M : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [q.IsLocallyFreeData] (i : q.I)
    {x : X} (hx : x ∈ q.X i) :
    Nonempty (Module.Basis (q.generators i).I (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :=
  (nonempty_stalkLinearEquiv_of_isLocallyFreeData M q i hx).elim
    fun e ↦ ⟨Module.Basis.ofRepr e⟩

/-- At a point of a member of locally free local generators data, the stalk is a free module over
the local ring. -/
theorem free_stalk_of_isLocallyFreeData (M : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [q.IsLocallyFreeData] (i : q.I)
    {x : X} (hx : x ∈ q.X i) :
    Module.Free (ToType (X.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  (nonempty_stalkBasis_of_isLocallyFreeData M q i hx).elim Module.Free.of_basis

/-- **The stalk of a locally free sheaf of modules on a scheme is free** over the local ring at
that point, with no finiteness hypothesis anywhere. In the numbering of Stacks Tag 05P2 this is
the stalkwise half of the implication (3) ⟹ (2); it is the statement whose absence
`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean` records as the obstruction to the
remaining implications of that tag. -/
theorem free_stalk_of_isLocallyFree (M : X.Modules)
    [hM : SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) M] (x : X) :
    Module.Free (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeData
  have := hq
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop q.X q.coversTop x
  exact free_stalk_of_isLocallyFreeData M q i hi

/-- **The rank-finiteness step of Stacks Tag 05P2, (3) ⟹ (4).** If the stalk of `M` at some
point of `q.X i` is a finite module over the local ring there, then the index type of the `i`-th
family of local generators is finite.

This is the shrinking argument of that implication, and it is exactly the step which has to be
run at the stalk: the local ring of a scheme is nontrivial, so a free module on `(q.generators
i).I` which is finitely generated forces `(q.generators i).I` to be finite. -/
theorem finite_index_of_isLocallyFreeData (M : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [q.IsLocallyFreeData] (i : q.I)
    {x : X} (hx : x ∈ q.X i)
    [Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))] :
    Finite (q.generators i).I :=
  (nonempty_stalkBasis_of_isLocallyFreeData M q i hx).elim fun b ↦
    Module.Finite.finite_basis b

/-- The stalk of a finite locally free sheaf of modules is a free module of finite rank over the
local ring. Stated over the tagged class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`; see the implementation notes. -/
theorem freeAndFinite_stalk_of_isFiniteLocallyFree (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M] (x : X) :
    Module.Free (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) ∧
      Module.Finite (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := by
  obtain ⟨q, hq, hqf⟩ := hM.exists_isFiniteLocallyFreeData
  have := hq
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop q.X q.coversTop x
  obtain ⟨b⟩ := nonempty_stalkBasis_of_isLocallyFreeData M q i hi
  have : Finite (q.generators i).I := (hqf.isFiniteType i).finite
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- Discarding the empty members of an open covering family leaves an open covering family. -/
theorem coversTop_subtype_nonempty {T : Type u} [TopologicalSpace T] {ι : Type w}
    (U : ι → Opens T) (hU : (Opens.grothendieckTopology T).CoversTop U) :
    (Opens.grothendieckTopology T).CoversTop (fun i : {i : ι // ∃ x, x ∈ U i} ↦ U i.1) := by
  refine (Opens.coversTop_iff _ _).2 (IsOpenCover.mk (eq_top_iff.2 (IsConcreteLE.le_iff.2 ?_)))
  intro x _
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop U hU x
  exact Opens.mem_iSup.2 ⟨⟨i, ⟨x, hi⟩⟩, hi⟩

/-- Local generators data with its empty members discarded. The members are the same, but only
those whose open set has a point are kept, which is what lets a finiteness statement proved at a
point of each member be read as finiteness of the whole family. -/
def dropEmpty {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} M) :
    SheafOfModules.LocalGeneratorsData.{w} M where
  I := {i : q.I // ∃ x : (X : TopCat.{u}), x ∈ q.X i}
  X i := q.X i.1
  coversTop := coversTop_subtype_nonempty q.X q.coversTop
  generators i := q.generators i.1

/-- If local generators data is locally free, then so is the data obtained by discarding its
empty members. -/
instance isLocallyFreeData_dropEmpty {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [hq : q.IsLocallyFreeData] :
    (dropEmpty q).IsLocallyFreeData where
  isIso i := hq.isIso i.1

/-- Once every stalk is a finite module, the nonempty members of locally free local generators
data are generated by finitely many sections. -/
theorem isFiniteType_dropEmpty (M : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [q.IsLocallyFreeData]
    (hfin : ∀ x : X, Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    (dropEmpty q).IsFiniteType where
  isFiniteType i :=
    have hx := i.2.choose_spec
    have := hfin i.2.choose
    ⟨finite_index_of_isLocallyFreeData M q i.1 hx⟩

/-- **Stacks Tag 05P2, the implication (3) ⟹ (4), reduced to one statement about stalks.** A
locally free sheaf of modules on a scheme all of whose stalks are finite modules over the local
ring is finite locally free.

This is the whole of that implication except for the step "a sheaf of modules of finite type has
finitely generated stalks", which is the only thing still missing: entry (3) of the tag is
`IsLocallyFree ∧ IsFiniteType`, and `IsFiniteType` is exactly what should supply `hfin`. The
shrinking that the tag's proof performs is the content of `finite_index_of_isLocallyFreeData`,
and the only further bookkeeping is to discard the members of the covering family that are
empty — on an empty open set a free chart of infinite rank is harmless but still violates
`IsFiniteType`, so those members must go, and discarding them does not change the union. -/
theorem isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk (M : X.Modules)
    [hM : SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) M]
    (hfin : ∀ x : X, Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeData
  have := hq
  constructor
  exact ⟨dropEmpty q, inferInstance, isFiniteType_dropEmpty M q hfin⟩

/-- The two copies of finite local freeness carried by the repository agree. This crosses from
the tagged library class to `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, off which the Tag
05P2 consequences already proved hang; it is a one-liner because the two classes have identical
bodies, and it exists so that nothing here needs a third copy. -/
theorem finiteLocallyFree_isFiniteLocallyFree (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M] :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M := by
  constructor
  exact hM.exists_isFiniteLocallyFreeData

/-- The converse of `finiteLocallyFree_isFiniteLocallyFree`. -/
theorem isFiniteLocallyFree_of_finiteLocallyFree (M : X.Modules)
    [hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M := by
  constructor
  exact hM.exists_isFiniteLocallyFreeData

end Stacks.StalkFreeBridge

end
