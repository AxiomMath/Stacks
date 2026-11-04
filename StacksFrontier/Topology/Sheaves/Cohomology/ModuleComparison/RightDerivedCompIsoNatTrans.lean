module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOnOpenDerived

/-!
# The composite right-derived comparison is natural in the derived functor

`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is the comparison
`F.rightDerived n ⋙ G ≅ H.rightDerived n` attached to an exact additive functor `G` and an
isomorphism `e : F ⋙ G ≅ H`.  `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_congr`
already records its naturality in the *outer* functor `G`.  This file records its naturality in
the *derived* variable: a natural transformation `α : F₁ ⟶ F₂` and a natural transformation
`β : H₁ ⟶ H₂` which agree under the two comparisons, in the sense that
`Functor.whiskerRight α G ≫ e₂.hom = e₁.hom ≫ β`, induce transformations of right derived
functors that again agree under the two comparisons.

This is the statement which lets a map of cohomology produced on one model of a cohomology
functor be recognised on another: if `H₁` and `H₂` are two functors computing the same
cohomology as `F₁ ⋙ G` and `F₂ ⋙ G`, then `CategoryTheory.NatTrans.rightDerived α n` and
`CategoryTheory.NatTrans.rightDerived β n` are the same morphism read through
`rightDerivedCompIso`.

## Main results

* `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_natTrans_compat`: **the
  comparison is natural in the derived functor.**  For `α : F₁ ⟶ F₂` and `β : H₁ ⟶ H₂` with
  `Functor.whiskerRight α G ≫ e₂.hom = e₁.hom ≫ β`,
  `Functor.whiskerRight (NatTrans.rightDerived α n) G ≫ (rightDerivedCompIso F₂ G H₂ e₂ n).hom`
  equals `(rightDerivedCompIso F₁ G H₁ e₁ n).hom ≫ NatTrans.rightDerived β n`.
* `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_natTrans_compat_app`: the same
  statement one object at a time.
* `Stacks.Cohomology.DerivedCompTransport.mapComplexHomologyIso_hom_app_natTransSource` and
  `Stacks.Cohomology.DerivedCompTransport.mapHomologicalComplexCompIso_hom_app_natTransSource`:
  the complex-level and the degreewise content out of which the previous two are built.
* `Stacks.Cohomology.ModuleComparison.sectionsOnOpenRestrict`: restriction of the sections of a
  sheaf of modules over an open of a ringed space to a smaller open, as a map of modules over
  the ring of *global* functions, and
  `Stacks.Cohomology.ModuleComparison.sectionsOnComplementRestrict`: its instance at the open
  complements of two nested closed subsets.
* `forget₂_rightDerived_sectionsOnOpen_restriction_eq_HrestrictNT` and
  `forget₂_rightDerived_sectionsOnComplement_restriction_eq_HrestrictNT`, in the namespace
  `Stacks.Cohomology.ModuleComparison`: **the two restriction maps on the cohomology of an open
  agree.**  The map that `CategoryTheory.NatTrans.rightDerived` produces from the restriction of
  module-valued sections is, under the comparison
  `Stacks.Cohomology.ModuleComparison.sectionsOnOpenForgetIso` with the abelian-group-valued
  cohomology functor, the restriction map `HrestrictNT` of Stacks 01E3.

## Implementation notes

The whole content is the naturality of
`Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso` in the complex, applied to the
degreewise image of `α`, together with the degreewise identity between the two isomorphisms of
functors, which `HomologicalComplex.hom_ext` reduces to the hypothesis.  Passing from the
complex level to `rightDerivedCompIso` is the cancellation of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` for `F₂` and for `H₁` against itself,
since `CategoryTheory.InjectiveResolution.rightDerived_app_eq` computes both transformations of
derived functors on the same chosen injective resolution that `rightDerivedCompIso` is built on.

As in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity`,
`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` is assembled from two whiskerings
meeting at an object that `F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c` and
`(F ⋙ G).mapHomologicalComplex c` spell differently; the two spellings are definitionally equal
but the composite is not type-correct at the `implicit` transparency that `rw` and `simp only`
match at, so the complex-level proof is a term built from `congrArg` and from the private
reassociation lemma `squareGlue`, whose hypotheses are exactly a commuting square and a
commuting triangle.

**The ringed-space instance.**  `Stacks.Cohomology.ModuleComparison.sectionsOnOpen` is
evaluation over the open followed by restriction of scalars along `Γ(X, 𝒪_X) → Γ(W, 𝒪_X)`, so a
restriction between two such functors is the restriction map of the sheaf of modules read along
the identification of the two restrictions of scalars, which is
`CategoryTheory.ModuleCat.restrictScalarsComp'App` for the factorization
`globalScalarsRestrict_comp` of the scalar restriction of the smaller open through that of the
larger.  Both the naturality of `sectionsOnOpenRestrict` and its compatibility with the
abelian-group-valued restriction are then statements about the underlying maps of sets, because
`CategoryTheory.ModuleCat.restrictScalarsComp'App` and
`CategoryTheory.ModuleCat.restrictScalars` leave those alone; they are proved by `ext` followed
by `CategoryTheory.PresheafOfModules.naturality_apply` and by `rfl`.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

open Stacks.Cohomology.ModuleComparison

/-! ### Reassociation -/

section Glue

variable {O : Type*} [Category* O]

/-- The reassociation behind `mapComplexHomologyIso_hom_app_natTransSource`: a commuting square
followed by a commuting triangle, with the right-hand composite read as a two-fold composite. -/
private theorem squareGlue {P Q R S T U : O} (a : P ⟶ Q) (i₂ : Q ⟶ R) (d₂ : R ⟶ U) (i₁ : P ⟶ S)
    (mu : S ⟶ R) (d₁ : S ⟶ T) (b : T ⟶ U) (hsquare : a ≫ i₂ = i₁ ≫ mu)
    (htriangle : mu ≫ d₂ = d₁ ≫ b) : a ≫ i₂ ≫ d₂ = (i₁ ≫ d₁) ≫ b := by
  rw [← Category.assoc, hsquare, Category.assoc, htriangle, ← Category.assoc]

/-- The reassociation behind `rightDerivedCompIso_natTrans_compat_app`: a commuting square with
a common factor appended on the right. -/
private theorem postGlue {P Q R S U : O} (a : P ⟶ Q) (c₂ : Q ⟶ R) (c₁ : P ⟶ S) (b : S ⟶ R)
    (k : R ⟶ U) (h : a ≫ c₂ = c₁ ≫ b) : a ≫ c₂ ≫ k = c₁ ≫ b ≫ k := by
  rw [← Category.assoc, h, Category.assoc]

end Glue

/-! ### The comparison on complexes -/

section Complexes

variable {A : Type*} {B : Type*} {D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]

/-- The degreewise content of `mapComplexHomologyIso_hom_app_natTransSource`: applying `G`
degreewise to `α` and following with `e₂` is `e₁` followed by `β`, degreewise. -/
theorem mapHomologicalComplexCompIso_hom_app_natTransSource {F₁ F₂ : A ⥤ B} (G : B ⥤ D)
    {H₁ H₂ : A ⥤ D} [F₁.Additive] [F₂.Additive] [G.Additive] [H₁.Additive] [H₂.Additive]
    (e₁ : F₁ ⋙ G ≅ H₁) (e₂ : F₂ ⋙ G ≅ H₂) (α : F₁ ⟶ F₂) (β : H₁ ⟶ H₂)
    (hα : ∀ X : A, G.map (α.app X) ≫ e₂.hom.app X = e₁.hom.app X ≫ β.app X)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) ≫
        (Functor.mapHomologicalComplexCompIso e₂ (ComplexShape.up ℕ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso e₁ (ComplexShape.up ℕ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app K := by
  ext n
  simpa using hα (K.X n)

/-- **`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` is natural in the derived
functor.**  A natural transformation `α : F₁ ⟶ F₂` and a natural transformation `β : H₁ ⟶ H₂`
compatible with `e₁` and `e₂` intertwine the two complex-level comparisons. -/
theorem mapComplexHomologyIso_hom_app_natTransSource {F₁ F₂ : A ⥤ B} (G : B ⥤ D)
    {H₁ H₂ : A ⥤ D} [F₁.Additive] [F₂.Additive] [G.Additive] [H₁.Additive] [H₂.Additive]
    [G.PreservesHomology] (e₁ : F₁ ⋙ G ≅ H₁) (e₂ : F₂ ⋙ G ≅ H₂) (α : F₁ ⟶ F₂) (β : H₁ ⟶ H₂)
    (hα : ∀ X : A, G.map (α.app X) ≫ e₂.hom.app X = e₁.hom.app X ≫ β.app X) (p : ℕ)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    G.map (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) p) ≫
        (mapComplexHomologyIso F₂ G H₂ e₂ p).hom.app K =
      (mapComplexHomologyIso F₁ G H₁ e₁ p).hom.app K ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app K) p :=
  squareGlue _ _ _ _ _ _ _
    ((homologyMapFunctorIso G p).inv.naturality
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K))
    (((HomologicalComplex.homologyMap_comp _ _ p).symm.trans
        (congrArg (fun φ => HomologicalComplex.homologyMap φ p)
          (mapHomologicalComplexCompIso_hom_app_natTransSource G e₁ e₂ α β hα K))).trans
      (HomologicalComplex.homologyMap_comp _ _ p))

end Complexes

/-! ### The comparison on right derived functors -/

section Derived

variable {A : Type*} {B : Type*} {D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]

/-- **`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is natural in the derived
functor, pointwise.**  See `rightDerivedCompIso_natTrans_compat` for the statement as an
equality of natural transformations. -/
theorem rightDerivedCompIso_natTrans_compat_app (F₁ F₂ : A ⥤ B) (G : B ⥤ D) (H₁ H₂ : A ⥤ D)
    [F₁.Additive] [F₂.Additive] [G.Additive] [H₁.Additive] [H₂.Additive] [G.PreservesHomology]
    (e₁ : F₁ ⋙ G ≅ H₁) (e₂ : F₂ ⋙ G ≅ H₂) (α : F₁ ⟶ F₂) (β : H₁ ⟶ H₂)
    (hcompat : Functor.whiskerRight α G ≫ e₂.hom = e₁.hom ≫ β) (n : ℕ) (M : A) :
    G.map ((NatTrans.rightDerived α n).app M) ≫
        (rightDerivedCompIso F₂ G H₂ e₂ n).hom.app M =
      (rightDerivedCompIso F₁ G H₁ e₁ n).hom.app M ≫ (NatTrans.rightDerived β n).app M := by
  have hα : ∀ X : A, G.map (α.app X) ≫ e₂.hom.app X = e₁.hom.app X ≫ β.app X := fun X => by
    simpa using NatTrans.congr_app hcompat X
  rw [rightDerivedCompIso_hom_app, rightDerivedCompIso_hom_app,
    InjectiveResolution.rightDerived_app_eq α (injectiveResolution M) n,
    InjectiveResolution.rightDerived_app_eq β (injectiveResolution M) n,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    Iso.map_inv_hom_id_assoc, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyFunctor_map, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact congrArg (fun g => G.map ((injectiveResolution M).isoRightDerivedObj F₁ n).hom ≫ g)
    (postGlue _ _ _ _ _
      (mapComplexHomologyIso_hom_app_natTransSource G e₁ e₂ α β hα n
        (injectiveResolution M).cocomplex))

/-- **`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` is natural in the derived
functor.**  Let `α : F₁ ⟶ F₂` and `β : H₁ ⟶ H₂` be natural transformations which agree under
the two comparisons, in the sense that `Functor.whiskerRight α G ≫ e₂.hom = e₁.hom ≫ β`.  Then
the transformations `CategoryTheory.NatTrans.rightDerived α n` and
`CategoryTheory.NatTrans.rightDerived β n` of right derived functors again agree under the two
comparisons. -/
theorem rightDerivedCompIso_natTrans_compat (F₁ F₂ : A ⥤ B) (G : B ⥤ D) (H₁ H₂ : A ⥤ D)
    [F₁.Additive] [F₂.Additive] [G.Additive] [H₁.Additive] [H₂.Additive] [G.PreservesHomology]
    (e₁ : F₁ ⋙ G ≅ H₁) (e₂ : F₂ ⋙ G ≅ H₂) (α : F₁ ⟶ F₂) (β : H₁ ⟶ H₂)
    (hcompat : Functor.whiskerRight α G ≫ e₂.hom = e₁.hom ≫ β) (n : ℕ) :
    Functor.whiskerRight (NatTrans.rightDerived α n) G ≫
        (rightDerivedCompIso F₂ G H₂ e₂ n).hom =
      (rightDerivedCompIso F₁ G H₁ e₁ n).hom ≫ NatTrans.rightDerived β n :=
  NatTrans.ext (funext fun M =>
    rightDerivedCompIso_natTrans_compat_app F₁ F₂ G H₁ H₂ e₁ e₂ α β hcompat n M)

end Derived

end Stacks.Cohomology.DerivedCompTransport

/-! ### Restriction of sections over an open of a ringed space -/

namespace Stacks.Cohomology.ModuleComparison

open AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport

universe u

variable (X : RingedSpace.{u, u})

/-- Restricting a global function of a ringed space to `U` is restricting it to a larger open
`V` and then restricting to `U`. -/
theorem globalScalarsRestrict_comp {U V : Opens X} (h : U ≤ V) :
    ((structureSheafRing X).obj.map (homOfLE (le_top : U ≤ ⊤)).op).hom =
      ((structureSheafRing X).obj.map (homOfLE h).op).hom.comp
        ((structureSheafRing X).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom := by
  have hop : (homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE h).op =
      (homOfLE (le_top : U ≤ ⊤)).op := rfl
  rw [← hop, (structureSheafRing X).obj.map_comp, RingCat.hom_comp]

/-- **Restriction of sections over an open of a ringed space, with the global scalars.**  For
`U ≤ V` this is the restriction map `Γ(V, -) ⟶ Γ(U, -)` of the sheaf of modules, read as a map of
modules over the ring `Γ(X, 𝒪_X)` of global functions.

The scalars of the two sides are restricted along `Γ(X, 𝒪_X) → Γ(V, 𝒪_X)` and along
`Γ(X, 𝒪_X) → Γ(U, 𝒪_X)` respectively, and `globalScalarsRestrict_comp` says that the second is
the first followed by `Γ(V, 𝒪_X) → Γ(U, 𝒪_X)`; the component is therefore the restriction map of
the module sheaf read along `CategoryTheory.ModuleCat.restrictScalarsComp'App`. -/
def sectionsOnOpenRestrict {U V : Opens X} (h : U ≤ V) :
    sectionsOnOpen X V ⟶ sectionsOnOpen X U where
  app F :=
    (ModuleCat.restrictScalars
          ((structureSheafRing X).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom).map
        (F.val.map (homOfLE h).op) ≫
      (ModuleCat.restrictScalarsComp'App
        ((structureSheafRing X).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom
        ((structureSheafRing X).obj.map (homOfLE h).op).hom
        ((structureSheafRing X).obj.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (globalScalarsRestrict_comp X h) (F.val.obj (op U))).inv
  naturality F G φ := by
    ext x
    exact (PresheafOfModules.naturality_apply φ.val (homOfLE h).op x).symm

/-- The open complement of a larger closed subset is contained in that of a smaller one. -/
theorem openComplement_le_openComplement {Z₁ Z₂ : Set X} (hZ₁ : IsClosed Z₁)
    (hZ₂ : IsClosed Z₂) (hZ : Z₁ ⊆ Z₂) : openComplement Z₂ hZ₂ ≤ openComplement Z₁ hZ₁ :=
  fun _ hx hx₁ => hx (hZ hx₁)

/-- **Restriction of sections from the complement of a smaller closed subset to the complement
of a larger one.**  For `Z₁ ⊆ Z₂` the open complement of `Z₂` is contained in that of `Z₁`, so
restriction goes from the sections on the complement of `Z₁` to those on the complement of `Z₂`.
This is the instance of `sectionsOnOpenRestrict` at the two open complements. -/
def sectionsOnComplementRestrict {Z₁ Z₂ : Set X} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (hZ : Z₁ ⊆ Z₂) : sectionsOnComplement X Z₁ hZ₁ ⟶ sectionsOnComplement X Z₂ hZ₂ :=
  sectionsOnOpenRestrict X (openComplement_le_openComplement X hZ₁ hZ₂ hZ)

/-- **Deriving the sections over an open with the global scalars and then forgetting the module
structure is the abelian-group-valued cohomology of that open.**  This is
`rightDerivedCompIso` for the identity comparison: `sectionsOnOpen X W` followed by the
forgetful functor to abelian groups *is* `secF (structureSheafRing X) W`.

`Stacks.LocalCohomologySequence.complementCohomologyForgetIso` is its instance at the open
complement of the vanishing locus of an ideal on an affine scheme. -/
def sectionsOnOpenForgetIso (W : Opens X) (n : ℕ) :
    (sectionsOnOpen X W).rightDerived n ⋙ forget₂ (GlobalModules X) AddCommGrpCat.{u} ≅
      (secF (structureSheafRing X) W).rightDerived n :=
  rightDerivedCompIso _ _ _ (Iso.refl _) n

/-- Forgetting the module structure takes the restriction of module-valued sections to the
restriction of abelian-group-valued sections: both are the restriction map of the sheaf. -/
theorem whiskerRight_sectionsOnOpenRestrict_forget₂ {U V : Opens X} (h : U ≤ V) :
    Functor.whiskerRight (sectionsOnOpenRestrict X h)
        (forget₂ (GlobalModules X) AddCommGrpCat.{u}) =
      secRestrict (structureSheafRing X) h :=
  NatTrans.ext (funext fun _ => by ext x; rfl)

/-- **The two restriction maps on the cohomology of an open agree.**  The map induced on
cohomology by restriction of the *module-valued* sections over `V` to those over `U`, read
through the comparison `sectionsOnOpenForgetIso` with the abelian-group-valued cohomology
functor, is the restriction map `HrestrictNT` of Stacks 01E3.

This is `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_natTrans_compat`, whose
compatibility hypothesis is `whiskerRight_sectionsOnOpenRestrict_forget₂`. -/
theorem forget₂_rightDerived_sectionsOnOpen_restriction_eq_HrestrictNT
    {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    Functor.whiskerRight (NatTrans.rightDerived (sectionsOnOpenRestrict X h) n)
          (forget₂ (GlobalModules X) AddCommGrpCat.{u}) ≫
        (sectionsOnOpenForgetIso X U n).hom =
      (sectionsOnOpenForgetIso X V n).hom ≫ HrestrictNT (structureSheafRing X) h n :=
  DerivedCompTransport.rightDerivedCompIso_natTrans_compat
    (sectionsOnOpen X V) (sectionsOnOpen X U) (forget₂ (GlobalModules X) AddCommGrpCat.{u})
    (secF (structureSheafRing X) V) (secF (structureSheafRing X) U) (Iso.refl _) (Iso.refl _)
    (sectionsOnOpenRestrict X h) (secRestrict (structureSheafRing X) h)
    (by
      refine NatTrans.ext (funext fun _ => ?_)
      ext x
      rfl) n

/-- **The two restriction maps on the cohomology of an open complement agree.**  For `Z₁ ⊆ Z₂`
the map induced on cohomology by restriction of the module-valued sections on the complement of
`Z₁` to those on the complement of `Z₂` is, under
`sectionsOnOpenForgetIso`, the restriction map `HrestrictNT` of Stacks 01E3 for the inclusion of
open complements.  This identifies the restriction of the local-cohomology development with the
one of the abelian-group-valued cohomology functor. -/
theorem forget₂_rightDerived_sectionsOnComplement_restriction_eq_HrestrictNT
    {Z₁ Z₂ : Set X} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hZ : Z₁ ⊆ Z₂) (n : ℕ) :
    Functor.whiskerRight
          (NatTrans.rightDerived (sectionsOnComplementRestrict X hZ₁ hZ₂ hZ) n)
          (forget₂ (GlobalModules X) AddCommGrpCat.{u}) ≫
        (sectionsOnOpenForgetIso X (openComplement Z₂ hZ₂) n).hom =
      (sectionsOnOpenForgetIso X (openComplement Z₁ hZ₁) n).hom ≫
        HrestrictNT (structureSheafRing X)
          (openComplement_le_openComplement X hZ₁ hZ₂ hZ) n :=
  forget₂_rightDerived_sectionsOnOpen_restriction_eq_HrestrictNT X
    (openComplement_le_openComplement X hZ₁ hZ₂ hZ) n

end Stacks.Cohomology.ModuleComparison

end
