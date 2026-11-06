module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIsoShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.Decode
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# An acyclic covering computes the derived global sections of a bounded below complex

Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be an open covering of `X` and let `K^•`
be a bounded below complex of `O_X`-modules such that `H^i(U_{i_0 … i_p}, K^q) = 0` for all
`i > 0` and all tuples `i_0, …, i_p` and degrees `q`. Then the comparison map

`Tot(Č^•(U, K^•)) ⟶ RΓ(X, K^•)`

of Tag 08BN is an isomorphism.

## Main definitions

* `Stacks.Cech.abelianSections`: sections of the abelian sheaf underlying a sheaf of modules
  over an open subset.
* `Stacks.Cech.cechSections` and `Stacks.Cech.cechSectionsInt`: the Čech cochains of the
  covering in a fixed degree, as a functor on sheaves of modules, for the nonnegatively graded
  and for the integer-indexed Čech complex.

## Main results

* `Stacks.Cech.rightAcyclic_cechSections`: a sheaf of modules acyclic on the intersections of
  the covering is right acyclic for the Čech cochains in each degree.
* `Stacks.Cech.isIso_globalSectionsToDerived_of_injective`: on a bounded below complex of
  injectives the canonical map from ordinary to derived global sections is invertible.
* `Stacks.Cech.isIso_cechToDerivedGlobalSections_app`: **[Stacks, Tag 0FLH]**.

## Implementation notes

The source deduces the tag from the spectral sequence of Tag 08BN. That spectral sequence is
`Stacks.Cech.exists_cechSpectralSequence`, but it is not usable here: its file *imports* this
one, for the injective-complex comparison `Stacks.Cech.isIso_globalSectionsToDerived_of_injective`
proved below, so deducing the tag from it would be circular. The route taken here is instead
the two-step comparison that Tag 08BN's map is built from: by
`Stacks.Cech.cechToDerivedComparison_app` the comparison at `K^•` is the Čech map of a
functorial injective resolution `K^• ⟶ L^•`, followed by three further maps of which all but
the unit of the right derived functor at `L^•` are invertible for free. So the tag reduces to
two statements.

First, that unit is invertible at `L^•`: every term of `L^•` is injective, hence right acyclic
for global sections, and a bounded below complex of right acyclic objects computes the right
derived functor (Leray's acyclicity lemma, in the form
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`).

Second, the Čech map `Tot(Č^•(U, K^•)) ⟶ Tot(Č^•(U, L^•))` is a quasi-isomorphism. In Čech
degree `p` the column of the Čech bicomplex is the functor `Č^p(U, -)` applied termwise, and
`Č^p(U, -)` is the product, over the tuples `x : Fin (p + 1) → I`, of the sections over the
intersection `U_x` that `x` indexes. Right derived functors commute with it, because evaluation
of presheaves and products of abelian groups are exact; so the acyclicity hypothesis makes
every term of `K^•` right acyclic for `Č^p(U, -)`, every term of `L^•` right acyclic because it
is injective, and the column map is a quasi-isomorphism by
`CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic`. Weibel's acyclic
assembly lemma then passes from the columns to the total complexes. It is used in the form
`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_lowerBound`, with an arbitrary lower
bound in the complex degree: the Čech degree is the *first* index of the bicomplex, so the
second index is the complex degree, and a bounded below complex is bounded by an arbitrary
integer rather than by `0`.

The vanishing hypothesis is stated with the right derived functors of the module-valued
sections functor `SheafOfModules.evaluation`, as in Tag 01ET, and is transported to the
abelian-group-valued one along the exact forgetful functor.

The common universe is the one the existing total Čech complex API is stated at.

## References

* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Evaluating a sheaf of modules at an object of the site is additive, being the forgetful
functor to presheaves of modules followed by evaluation. -/
local instance additive_sheafOfModulesEvaluation
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : (Opens X)ᵒᵖ) :
    (SheafOfModules.evaluation.{u} R V).Additive :=
  inferInstanceAs (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V).Additive

/-- A sheaf of modules, read as an abelian presheaf. -/
noncomputable abbrev underlyingPresheafFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.{u} R ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj

/-- Sections over an open subset of the abelian sheaf underlying a sheaf of modules. -/
noncomputable abbrev abelianSections
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  underlyingPresheafFunctor X R ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The higher cohomology of the underlying abelian sheaf over an open subset vanishes as soon
as the module-valued one does.** -/
theorem isZero_rightDerived_abelianSections
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (V : Opens X)
    (A : SheafOfModules.{u} R) (i : ℕ)
    (h : IsZero (((SheafOfModules.evaluation.{u} R (op V)).rightDerived i).obj A)) :
    IsZero (((abelianSections X R V).rightDerived i).obj A) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.evaluation.{u} R (op V))
    (forget₂ (ModuleCat.{u} (R.obj.obj (op V))) AddCommGrpCat.{u}) i A
  exact IsZero.of_iso (Functor.map_isZero _ h) e.symm

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The presheaf of higher cohomology of a sheaf of modules vanishes over an open subset on
which the sheaf is acyclic. -/
theorem isZero_rightDerived_underlyingPresheaf_obj
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (V : Opens X)
    (A : SheafOfModules.{u} R) (i : ℕ)
    (h : IsZero (((SheafOfModules.evaluation.{u} R (op V)).rightDerived i).obj A)) :
    IsZero ((((underlyingPresheafFunctor X R).rightDerived i).obj A).obj (op V)) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (underlyingPresheafFunctor X R)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) i A
  exact IsZero.of_iso (isZero_rightDerived_abelianSections X V A i h) e

/-! ### The Čech cochains in a fixed degree -/

section CechTerm

variable {I : Type u} (U : I → Opens X)

/-- A product of zero objects is zero. -/
private lemma isZero_pi {J : Type u} (f : J → AddCommGrpCat.{u}) (h : ∀ j, IsZero (f j)) :
    IsZero (∏ᶜ f) := by
  rw [IsZero.iff_id_eq_zero]
  refine Limits.Pi.hom_ext _ _ fun j => ?_
  rw [Category.id_comp, Limits.zero_comp]
  exact (h j).eq_of_tgt _ _

/-- The family, indexed by the tuples of members of the covering, whose product is the Čech
cochains of an abelian presheaf in a fixed degree. -/
noncomputable def cechFamilyFunctor (n : ℕ) :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      (Discrete (Fin (n + 1) → I) ⥤ AddCommGrpCat.{u}) where
  obj P := Discrete.functor (Stacks.CechGaps.cechDeg U P n)
  map α := Discrete.natTrans fun x => α.app (op (∏ᶜ (U ∘ x.as)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Čech cochains of an abelian presheaf in a fixed nonnegative degree. -/
noncomputable abbrev cechTermFunctorAb (n : ℕ) :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{u}) U ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (up ℕ) n

/-- **The Čech cochains of an abelian presheaf in a fixed degree are the product, over the
tuples of members of the covering, of its sections over the intersections they index.** -/
noncomputable def cechTermIsoFamily (n : ℕ) :
    cechTermFunctorAb X U n ≅ cechFamilyFunctor X U n ⋙ lim :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

instance preservesFiniteLimits_cechFamilyFunctor (n : ℕ) :
    PreservesFiniteLimits (cechFamilyFunctor X U n) :=
  preservesFiniteLimits_of_evaluation _ fun j => inferInstanceAs (PreservesFiniteLimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (∏ᶜ (U ∘ j.as)))))

instance preservesFiniteColimits_cechFamilyFunctor (n : ℕ) :
    PreservesFiniteColimits (cechFamilyFunctor X U n) :=
  preservesFiniteColimits_of_evaluation _ fun j => inferInstanceAs (PreservesFiniteColimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (∏ᶜ (U ∘ j.as)))))

instance preservesFiniteLimits_cechTermFunctorAb (n : ℕ) :
    PreservesFiniteLimits (cechTermFunctorAb X U n) :=
  preservesFiniteLimits_of_natIso (cechTermIsoFamily X U n).symm

instance preservesFiniteColimits_cechTermFunctorAb (n : ℕ) :
    PreservesFiniteColimits (cechTermFunctorAb X U n) :=
  preservesFiniteColimits_of_natIso (cechTermIsoFamily X U n).symm

instance preservesHomology_cechTermFunctorAb (n : ℕ) :
    (cechTermFunctorAb X U n).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The Čech cochains of the covering in a fixed nonnegative degree, as a functor on sheaves of
modules. -/
noncomputable abbrev cechSections
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (n : ℕ) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  underlyingPresheafFunctor X R ⋙ cechTermFunctorAb X U n

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **A sheaf of modules whose higher cohomology vanishes on the intersections of the covering
is right acyclic for the Čech cochains in each degree.** -/
theorem rightAcyclic_cechSections
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (n : ℕ)
    (A : SheafOfModules.{u} R)
    (h : ∀ (s : Fin (n + 1) → I) (i : ℕ), 0 < i →
      IsZero (((SheafOfModules.evaluation.{u} R (op (⨅ k, U (s k)))).rightDerived i).obj A)) :
    (cechSections X U R n).rightAcyclic A := by
  rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
  intro i hi
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (underlyingPresheafFunctor X R) (cechTermFunctorAb X U n) i A
  refine IsZero.of_iso ?_ e.symm
  refine isZero_pi _ fun x => ?_
  have hz := h x i hi
  rw [← Stacks.CechGaps.prodOpens_eq_iInf U x] at hz
  exact isZero_rightDerived_underlyingPresheaf_obj X _ A i hz

/-! ### The columns of the Čech bicomplex -/

/-- The Čech cochains of the covering in a fixed integer degree, as a functor on sheaves of
modules. This is the column of the Čech bicomplex in that Čech degree. -/
noncomputable abbrev cechSectionsInt
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (p : ℤ) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  underlyingPresheafFunctor X R ⋙ cechComplexFunctorInt U ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) p

/-- In a Čech degree in the range of the embedding, the integer-indexed Čech cochains are the
nonnegatively graded ones. -/
noncomputable def cechSectionsIntIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {n : ℕ} {p : ℤ}
    (hp : embeddingUpNat.f n = p) :
    cechSectionsInt X U R p ≅ cechSections X U R n :=
  Functor.isoWhiskerLeft (underlyingPresheafFunctor X R ⋙
      CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{u}) U)
    (embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{u} hp)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- In negative Čech degree the Čech cochains of a complex of sheaves of modules vanish. -/
private lemma isZero_cechSectionsInt_obj
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (p : ℤ) (hp : p < 0)
    (M : CochainComplex (SheafOfModules.{u} R) ℤ) :
    IsZero (((cechSectionsInt X U R p).mapHomologicalComplex (up ℤ)).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ fun q => ?_
  refine (HomologicalComplex.isZero_extend_X
    ((CategoryTheory.cechComplexFunctor U).obj ((underlyingPresheafFunctor X R).obj (M.X q)))
    embeddingUpNat p fun i => ?_).eq_of_src _ _
  have hi : embeddingUpNat.f i = (i : ℤ) := rfl
  rw [hi]
  omega

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The column of the Čech bicomplex in a Čech degree is the Čech cochain functor in that
degree, applied termwise to the complex of coefficients.** -/
lemma cechBicomplexFunctor_map_f
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : K ⟶ L) (p : ℤ) :
    ((cechBicomplexFunctor U).map ((underlyingPresheafComplexFunctor X R).map φ)).f p =
      ((cechSectionsInt X U R p).mapHomologicalComplex (up ℤ)).map φ :=
  rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The Čech cochains in a fixed nonnegative degree carry a quasi-isomorphism of bounded below
complexes to a quasi-isomorphism**, when the source is acyclic on the intersections of the
covering and the target has injective terms. -/
theorem quasiIso_cechSections_map
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (n : ℕ)
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L)
    (hLinj : ∀ q : ℤ, Injective (L.X q))
    (hacyclic : ∀ (s : Fin (n + 1) → I) (q : ℤ) (i : ℕ), 0 < i →
      IsZero (((SheafOfModules.evaluation.{u} R
        (op (⨅ k, U (s k)))).rightDerived i).obj (K.X q))) :
    QuasiIso (((cechSections X U R n).mapHomologicalComplex (up ℤ)).map φ) :=
  Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic _ φ hK hL
    (fun q => rightAcyclic_cechSections X U R n (K.X q) fun s i hi => hacyclic s q i hi)
    (fun q => have := hLinj q; Functor.rightAcyclic_of_injective _ _)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The Čech cochains in a fixed integer degree carry a quasi-isomorphism of bounded below
complexes to a quasi-isomorphism.** In negative Čech degrees both complexes vanish. -/
theorem quasiIso_cechSectionsInt_map
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (p : ℤ)
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L)
    (hLinj : ∀ q : ℤ, Injective (L.X q))
    (hacyclic : ∀ (n : ℕ) (s : Fin (n + 1) → I) (q : ℤ) (i : ℕ), 0 < i →
      IsZero (((SheafOfModules.evaluation.{u} R
        (op (⨅ k, U (s k)))).rightDerived i).obj (K.X q))) :
    QuasiIso (((cechSectionsInt X U R p).mapHomologicalComplex (up ℤ)).map φ) := by
  rcases lt_or_ge p 0 with hneg | hpos
  · have hzero := isZero_cechSectionsInt_obj X U R p hneg
    have hiso : IsIso (((cechSectionsInt X U R p).mapHomologicalComplex (up ℤ)).map φ) := by
      have he : ((cechSectionsInt X U R p).mapHomologicalComplex (up ℤ)).map φ =
          ((hzero K).iso (hzero L)).hom := (hzero K).eq_of_src _ _
      rw [he]
      infer_instance
    infer_instance
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have hq := quasiIso_cechSections_map X U R n φ hK hL hLinj (fun s q i hi =>
      hacyclic n s q i hi)
    let α := NatIso.mapHomologicalComplex
      (cechSectionsIntIso X U R (n := n) (p := (n : ℤ)) rfl) (up ℤ)
    have hnat : ((cechSectionsInt X U R (n : ℤ)).mapHomologicalComplex (up ℤ)).map φ =
        α.hom.app K ≫ ((cechSections X U R n).mapHomologicalComplex (up ℤ)).map φ ≫
          α.inv.app L := by
      rw [← Category.assoc, ← α.hom.naturality φ, Category.assoc, α.hom_inv_id_app,
        Category.comp_id]
    rw [hnat]
    infer_instance

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The terms of the Čech bicomplex of a complex of sheaves of modules vanish in negative Čech
degree. -/
lemma isZero_cechBicomplex_X
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (p : ℤ) (hp : p < 0) :
    IsZero (((cechBicomplexFunctor U).obj
      ((underlyingPresheafComplexFunctor X R).obj K)).X p) :=
  isZero_cechSectionsInt_obj X U R p hp K

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The terms of the Čech bicomplex of a complex of sheaves of modules vanish wherever the
complex does, in each Čech degree. -/
lemma isZero_cechBicomplex_X_X
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (p q : ℤ) (hq : IsZero (K.X q)) :
    IsZero ((((cechBicomplexFunctor U).obj
      ((underlyingPresheafComplexFunctor X R).obj K)).X p).X q) :=
  Functor.map_isZero (cechSectionsInt X U R p) hq

/-! ### From the columns to the total complex -/

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The Čech map of a quasi-isomorphism into a complex of injectives is a quasi-isomorphism on
total complexes**, when the source is acyclic on the intersections of the covering. -/
theorem quasiIso_cechTotalComplexFunctor_map
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L) (a : ℤ)
    (hKz : ∀ q : ℤ, q < a → IsZero (K.X q)) (hLz : ∀ q : ℤ, q < a → IsZero (L.X q))
    (hLinj : ∀ q : ℤ, Injective (L.X q))
    (hacyclic : ∀ (n : ℕ) (s : Fin (n + 1) → I) (q : ℤ) (i : ℕ), 0 < i →
      IsZero (((SheafOfModules.evaluation.{u} R
        (op (⨅ k, U (s k)))).rightDerived i).obj (K.X q))) :
    QuasiIso ((cechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map φ)) := by
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_lowerBound _ 0 a
    (fun p q hq => isZero_cechBicomplex_X_X X U R K p q (hKz q hq))
    (fun p hp => isZero_cechBicomplex_X X U R K p hp)
    (fun p q hq => isZero_cechBicomplex_X_X X U R L p q (hLz q hq))
    (fun p hp => isZero_cechBicomplex_X X U R L p hp) fun p => ?_
  rw [cechBicomplexFunctor_map_f]
  exact quasiIso_cechSectionsInt_map X U R p φ hK hL hLinj hacyclic

/-! ### Derived global sections of a complex of injectives -/

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The canonical map from ordinary to derived global sections, written out as the composite of
its five factors. -/
private theorem globalSectionsToDerivedNat_app_eq
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (L : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (globalSectionsToDerivedNat X R).app L =
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
          ((CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
            (abelianGlobalSections X R).mapHomologicalComplex (up ℤ)).obj L) ≫
        (DerivedCategory.Qh (C := AddCommGrpCat.{u})).map
          ((globalSectionsHomotopyBridgeIso X R).inv.app L) ≫
        (DerivedCategory.Plus.QhCompιIsoιCompQh AddCommGrpCat.{u}).inv.app
          ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
            (abelianGlobalSections X R).mapHomotopyCategoryPlus).obj L) ≫
        (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})).map
          ((abelianGlobalSections X R).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R)).obj L)) ≫
        (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})).map
          ((abelianGlobalSections X R).rightDerivedFunctorPlus.map
            ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
              (SheafOfModules.{u} R)).hom.app L)) :=
  rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **On a bounded below complex of injectives the canonical map from ordinary to derived global
sections is invertible.** -/
theorem isIso_globalSectionsToDerived_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (L : CochainComplex.Plus (SheafOfModules.{u} R))
    (hL : ∀ n : ℤ, Injective (L.1.X n)) :
    IsIso ((globalSectionsToDerivedNat X R).app L) := by
  have hunit : IsIso ((abelianGlobalSections X R).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R)).obj L)) := by
    refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n => ?_
    have := hL n
    exact Functor.rightAcyclic_of_injective _ _
  rw [globalSectionsToDerivedNat_app_eq]
  have h2 : IsIso ((globalSectionsHomotopyBridgeIso X R).inv.app L) := inferInstance
  have h5 : IsIso ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} R)).hom.app L) := inferInstance
  refine IsIso.comp_isIso'
    (Iso.isIso_hom ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app _).symm)
    (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ?_ ?_)))
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Qh (C := AddCommGrpCat.{u})) _ h2
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})) _ hunit
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})) _
      (@Functor.map_isIso _ _ _ _ _ _
        (abelianGlobalSections X R).rightDerivedFunctorPlus _ h5)

/-! ### The tag -/

/-- **[Stacks, Tag 0FLH]** Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be an open
covering of `X` and let `K^•` be a bounded below complex of `O_X`-modules with
`H^i(U_{i_0 … i_p}, K^q) = 0` for all `i > 0`, all tuples `i_0, …, i_p` of members of the
covering, and all degrees `q`. Then the comparison map `Tot(Č^•(U, K^•)) ⟶ RΓ(X, K^•)` of
Tag 08BN is an isomorphism. -/
@[stacks 0FLH "the vanishing condition is the one of Tag 01ET: the higher right derived
functors of sections over each intersection vanish on each term of the complex"]
theorem isIso_cechToDerivedGlobalSections_app
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R))
    (hacyclic : ∀ (n : ℕ) (s : Fin (n + 1) → I) (q : ℤ) (i : ℕ), 0 < i →
      IsZero (((SheafOfModules.evaluation.{u} R
        (op (⨅ k, U (s k)))).rightDerived i).obj (K.1.X q))) :
    IsIso (((cechToDerivedGlobalSections X R).map U hU).app K) := by
  set L := (injectiveResolutionFunctor X R).obj K with hLdef
  set f := (injectiveResolutionUnit X R).app K with hfdef
  have hqi : QuasiIso f.hom := injectiveResolution_quasiIso X R K
  have hLinj : ∀ q : ℤ, Injective (L.1.X q) := fun q => by
    show Injective ((InjectiveObject.ι (SheafOfModules.{u} R)).obj _)
    infer_instance
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff _ L.1).mp L.2
  have hKz : ∀ q : ℤ, q < min a b → IsZero (K.1.X q) := fun q hq =>
    (CochainComplex.isStrictlyGE_iff K.1 a).mp ha q (lt_of_lt_of_le hq (min_le_left a b))
  have hLz : ∀ q : ℤ, q < min a b → IsZero (L.1.X q) := fun q hq =>
    (CochainComplex.isStrictlyGE_iff L.1 b).mp hb q (lt_of_lt_of_le hq (min_le_right a b))
  have hcech : IsIso ((cechDerivedFunctor X R U).map f) := by
    have hq : QuasiIso ((cechTotalComplexFunctor U).map
        ((underlyingPresheafComplexFunctor X R).map f.hom)) :=
      quasiIso_cechTotalComplexFunctor_map X U R f.hom K.2 L.2 (min a b) hKz hLz hLinj
        hacyclic
    show IsIso (DerivedCategory.Q.map ((cechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map f.hom)))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hunit : IsIso ((globalSectionsToDerivedNat X R).app L) :=
    isIso_globalSectionsToDerived_of_injective X R L hLinj
  show IsIso ((cechToDerivedComparison X R U hU).app K)
  rw [cechToDerivedComparison_app]
  infer_instance

end CechTerm

end Stacks.Cech

end
