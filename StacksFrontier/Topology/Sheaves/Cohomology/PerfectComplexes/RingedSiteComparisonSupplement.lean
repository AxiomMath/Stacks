module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatFinitelyPresentedSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy

/-!
# Further results on `RingedSiteComparison`

Results about the objects of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A direct summand of a finite free module on an open subspace is one on the slice over that
open.** The two conditions differ only in the spelling of a finite free module: on the space it is
the biproduct of `n` copies of the structure sheaf, on the site the free module on
`ULift (Fin n)`, and `StrictlyPerfect.finiteFreeIsoFree` identifies the two. The retract exhibiting
the summand is carried across the equivalence of the two categories of modules, which takes the
structure sheaf to the unit of the slice sheaf of rings on the nose. -/
theorem isDirectSummandOfFiniteFree_slice_of_isDirectSummandOfFiniteFree (V : Opens X.carrier)
    {M : OXMod.{u, u} (X.restrict V.isOpenEmbedding)}
    (hM : StrictlyPerfect.IsDirectSummandOfFiniteFree M) :
    IsDirectSummandOfFiniteFree ((structureSheafOfRings X).over V)
      ((PseudoCoherence.sheafOfModulesEquivRestrict X V).inverse.obj M) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract M).mp hM
  set e := PseudoCoherence.sheafOfModulesEquivRestrict X V
  let I := ULift.{u} (Fin n)
  let eFin : e.inverse.obj (finiteFree (X.restrict V.isOpenEmbedding) n) ≅
      SheafOfModules.free (R := (structureSheafOfRings X).over V) I :=
    e.inverse.mapIso (finiteFreeIsoFree (X.restrict V.isOpenEmbedding) n ≪≫
      SheafOfModules.mapFreeIso e.functor I (Iso.refl _)) ≪≫ (e.unitIso.app _).symm
  have ρ' : Retract (e.inverse.obj M)
      (SheafOfModules.free (R := (structureSheafOfRings X).over V) I) :=
    (ρ.map e.inverse).trans (Retract.ofIso eFin)
  exact Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free _ _ I
    ρ'.i ρ'.r ρ'.retract

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A strictly perfect complex on an open subspace is strictly perfect on the slice over that
open.** Degreewise this is the previous statement; boundedness is preserved because the
identification of the two categories of modules takes a zero object to a zero object. -/
theorem isStrictlyPerfect_slice_of_isStrictlyPerfect (V : Opens X.carrier)
    {P : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ}
    (hP : StrictlyPerfect.IsStrictlyPerfect P) :
    IsStrictlyPerfect ((structureSheafOfRings X).over V)
      (((PseudoCoherence.sheafOfModulesEquivRestrict X V).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz => hi
    (Functor.map_isZero (PseudoCoherence.sheafOfModulesEquivRestrict X V).inverse hz)
  termDirectSummand i :=
    isDirectSummandOfFiniteFree_slice_of_isDirectSummandOfFiniteFree X V (hP.directSummand i)

/-- **A quasi-isomorphism stays one after an additive functor preserving homology, followed by an
isomorphism of the target.** -/
private theorem exists_quasiIso_map_trans {𝒞 : Type*} [Category* 𝒞] [Preadditive 𝒞]
    [CategoryWithHomology 𝒞] {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟]
    [CategoryWithHomology 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.PreservesHomology]
    {Q A : CochainComplex 𝒞 ℤ} (q : Q ⟶ A) (hq : QuasiIso q) {B : CochainComplex 𝒟 ℤ}
    (i : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ≅ B) :
    ∃ q' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶ B, QuasiIso q' := by
  have := hq
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ i.hom, inferInstance⟩

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A strictly perfect model over an open subspace gives one on the slice over any smaller
open.** Restrict the model and the quasi-isomorphism along `V ≤ U`, which preserves strict
perfectness and, being exact, quasi-isomorphisms; then carry both across the identification of the
modules on `X|_V` with the modules on the slice over `V`, under which the restriction of the
complex to `X|_V` is the restriction of the complex to the slice. -/
theorem exists_isStrictlyPerfect_quasiIso_of_le
    (E : CochainComplex (OXMod.{u, u} X) ℤ) {V U : Opens X.carrier} (h : V ≤ U)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (f : P ⟶ StrictlyPerfect.restrictComplex.{u} E U) (hf : QuasiIso f) :
    ∃ Q : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over V)) ℤ,
      IsStrictlyPerfect ((structureSheafOfRings X).over V) Q ∧
        ∃ q : Q ⟶ (ringedSite X).restrictComplex E V, QuasiIso q := by
  let : PreservesFiniteLimits (restrictModulesOfLE.{u} h (X := X)) :=
    preservesFiniteLimits_restrictModulesOfLE.{u} h
  let : PreservesFiniteColimits (restrictModulesOfLE.{u} h (X := X)) :=
    preservesFiniteColimits_restrictModulesOfLE.{u} h
  let : (restrictModulesOfLE.{u} h (X := X)).PreservesHomology := inferInstance
  let : (PseudoCoherence.sheafOfModulesEquivRestrict X V).inverse.PreservesHomology :=
    inferInstance
  obtain ⟨q₁, hq₁⟩ := exists_quasiIso_map_trans (restrictModulesOfLE.{u} h (X := X)) f hf
    (restrictComplexOfLEIso.{u} h E)
  obtain ⟨q₂, hq₂⟩ := exists_quasiIso_map_trans
    (PseudoCoherence.sheafOfModulesEquivRestrict X V).inverse q₁ hq₁
    ((NatIso.mapHomologicalComplex
      (PseudoCoherence.sheafOfModulesEquivRestrict X V).unitIso (ComplexShape.up ℤ)).app
      ((ringedSite X).restrictComplex E V)).symm
  exact ⟨_, isStrictlyPerfect_slice_of_isStrictlyPerfect X V
    (isStrictlyPerfect_restrictComplexOfLE.{u} h hP), q₂, hq₂⟩

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A perfect complex of `𝒪_X`-modules on a ringed space is a perfect complex on the ringed site
of its opens**: [Stacks, Tag 08CM] implies [Stacks, Tag 08G5] read along
`AlgebraicGeometry.RingedSpace.ringedSite`.

The presieve chosen on an open `W` is the sieve of the opens `V ≤ W` contained in a member of the
covering family of Tag 08CM. It covers `W`: a point of `W` lies in some member `U i` of that
family, the family having supremum `⊤`, and `W ⊓ U i` is a member of the presieve containing it.
Over such a `V` the strictly perfect model is the one given over `U i`, restricted to the slice
over `V` by `exists_isStrictlyPerfect_quasiIso_of_le`. -/
theorem isPerfectComplex_ringedSite_of_isPerfectComplex
    (E : CochainComplex (OXMod.{u, u} X) ℤ)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex E) :
    (ringedSite X).IsPerfectComplex E := by
  obtain ⟨I, U, hU, hcov⟩ := hE
  intro W
  refine ⟨fun V (_ : V ⟶ W) => ∃ i, V ≤ U i, ?_, ?_⟩
  · refine (Opens.mem_grothendieckTopology X.carrier).2 fun x hx => ?_
    have hxtop : x ∈ iSup U := hU ▸ trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxtop
    exact ⟨W ⊓ U i, homOfLE inf_le_left,
      ⟨W ⊓ U i, 𝟙 _, homOfLE inf_le_left, ⟨i, inf_le_right⟩, Subsingleton.elim _ _⟩,
      ⟨hx, hi⟩⟩
  · rintro V g ⟨i, hi⟩
    obtain ⟨P, hP, f, hf⟩ := hcov i
    exact exists_isStrictlyPerfect_quasiIso_of_le X E hi P hP f hf

/-- The chosen model of the derived category of the `𝒪_X`-modules, read at the ringed-site
spelling of the structure sheaf of rings. The two spellings are the same category but are not
reducibly equal, so instance search does not cross between them. -/
local instance hasDerivedCategoryRingedSite [inst : HasDerivedCategory.{d} (OXMod.{u, u} X)] :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :=
  inst

/-- **A perfect object of the derived category of `𝒪_X`-modules on a ringed space is a perfect
object on the ringed site of its opens**: [Stacks, Tag 08CM] implies [Stacks, Tag 08G5] for objects
of the derived category, read along `AlgebraicGeometry.RingedSpace.ringedSite`. Both predicates ask
for a representative which is a perfect complex, so this is
`isPerfectComplex_ringedSite_of_isPerfectComplex` on that representative. -/
theorem isPerfect_ringedSite_of_isPerfect [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    (ringedSite X).IsPerfect K := by
  obtain ⟨E, hE, ⟨i⟩⟩ := hK
  exact ⟨E, isPerfectComplex_ringedSite_of_isPerfectComplex X E hE, ⟨i⟩⟩

end AlgebraicGeometry.RingedSpace

end
