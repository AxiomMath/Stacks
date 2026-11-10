module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenSectionsDictionaryFrom
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.SiteComparison

/-!
# On one affine scheme: pseudo-coherence on the small étale site is pseudo-coherence of `RΓ(T, -)`

Let `T` be an affine scheme and let `E₀` be an object of `D(𝒪_T)` all of whose cohomology sheaves
are quasi-coherent.  Then, in each degree separately, `ε^*E₀` is `m`-pseudo-coherent on the small
étale site of `T` exactly when the complex `RΓ(T, E₀)` of `Γ(T, 𝒪_T)`-modules is
`m`-pseudo-coherent.

This is the scheme-side half of the derived-sections dictionary at an affine étale chart of an
algebraic space — item (iii) of the display in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean` — with the
chart and the algebraic space removed: the chart comparisons of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` have carried both sides
of that item to the small étale site of the chart's *scheme*, and what is left is a statement
about one affine scheme.  It is stated in a fixed degree because that is the only form the
locality criterion the chart-level statement is assembled over,
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, exists in; there is no
all-degrees locality criterion, so the all-degrees forms of the links would not compose into
anything the assembly could consume.

## Main results

* `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top`: on an affine scheme
  `T`, `m`-pseudo-coherence of `E₀` on the ringed space `T` is `m`-pseudo-coherence of the complex
  `RΓ(T, E₀)` of `Γ(T, 𝒪_T)`-modules.  This is Stacks 08E7 at the affine open `⊤`.
* The statement of the header is
  `AlgebraicGeometry.isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top`
* `AlgebraicGeometry.exists_derived_associatedModuleOfSheaf_iso`: **Stacks 071Q** read as
  essential surjectivity of `ε^*` on `D_QCoh` — an object of the derived category of `𝒪`-modules
  on the small étale site of a scheme with quasi-coherent cohomology is `ε^*E₀` for some `E₀` of
  `D(𝒪_T)` with quasi-coherent cohomology.
* `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top_of_iso`: the header's
  statement read at the object the small étale site carries rather than at `ε^*E₀`, the
  isomorphism being absorbed by
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso`.  With the previous result this is
  the whole scheme side of item (iii) of the display in the module documentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`, except
  for the identification of `RΓ(T, E₀)` with derived sections of the étale-side object at the
  final object of the site — comparison (ii) of that display, which is not composed here.

## How it is proved

Both are compositions of statements already in the library; nothing here is new mathematics.

The first is `AlgebraicGeometry.isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded`
— Stacks 08E7 at an affine open in a fixed degree — applied at the affine open `⊤`, whose
restriction has to be undone.  That restriction is along `⊤.ι`, which is an isomorphism (it is the
`hom` of `AlgebraicGeometry.Scheme.topIso`), so
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff` (Stacks 09VA at an
isomorphism in a fixed degree) carries the condition back along the pushforward, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompPushforwardIso` says the restriction followed
by that pushforward is the identity.  Reading the latter on derived categories is
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso` followed by
`CategoryTheory.Functor.mapDerivedCategoryId`, exactly as in
`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedTilde_derivedSectionsSpec`; no equivalence of
categories and no coherence condition is needed.

The second composes that with the two remaining legs on the scheme side:
`AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule` — **Stacks 08HE** in a fixed
degree — between the small étale site and the small Zariski site, and
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff` between the small Zariski
site and the underlying ringed space.  Each of the three is a biconditional, so the composite is
one too and both directions come out at once.

Stacks 071Q enters as `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, which
is an equivalence between the two `D_QCoh` full subcategories and carries no hypothesis beyond the
two derived-category models — in particular no essential-surjectivity side condition and no
`IsEquivalence` binder on the comparison with `D(QCoh)`.  Essential surjectivity is then
`CategoryTheory.Functor.objObjPreimageIso`, and the inclusion of the subcategory carries the
isomorphism it produces down to the ambient derived category.

## Implementation notes

`IsIso ⊤.ι` is **not** an instance, and is taken here as `AlgebraicGeometry.Scheme.topIso_hom`
rewritten into `CategoryTheory.Iso.isIso_hom` of `AlgebraicGeometry.Scheme.topIso`.  Substituting
the equation with `▸` instead does not work: it fails to compute a motive, the morphism occurring
in the types of both functors of the composite.

The two ambient-universe instances answering `Abelian` and `IsGrothendieckAbelian` for sheaves of
modules are removed for this file.  They fix the module universe to the join of the universes of
the site and of the rings, so a search for the abelian structure on the sheaves of modules of the
small étale site that reaches one of them first ends in `stuck at solving universe constraint
u + 1 =?= max (u + 1) ?u` rather than in a recoverable failure — as happens on the statement of the
second result below, which does not elaborate with them in scope.  The same removal is made, for
the same reason, in `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSliceKInjective` and in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteSiteAssembly`.

The derived-category model of the sheaves of modules on the small étale site is left to
`CategoryTheory.HasDerivedCategory.standard` rather than carried as a binder.  Carried, it is
reported as not definitionally equal to what the statement's own elaboration infers, the
pseudo-coherence predicate of the ringed site resolving the model at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling while the binder states it at
`AlgebraicGeometry.SmallEtale.structureSheaf`.

No `stacks` tag is placed: these are Stacks 08HE, Stacks 08E7 and Stacks 09VA composed, and the
bare attributes for all of them sit on their own statements.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **Stacks 08E7 at the whole of an affine scheme, in a fixed degree.**  Let `T` be an affine
scheme, let `E` be an object of `D(𝒪_T)` all of whose cohomology sheaves are quasi-coherent and
let `m` be an integer.  Then `E` is `m`-pseudo-coherent on the ringed space `T` if and only if the
complex `RΓ(T, E)` of `Γ(T, 𝒪_T)`-modules is `m`-pseudo-coherent.

This is `AlgebraicGeometry.isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded` at
the affine open `⊤`, with the restriction along `⊤.ι` undone; see "How it is proved" in the module
documentation. -/
public theorem isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top {T : Scheme.{u}} [IsAffine T]
    (E : DerivedCategory T.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := T.toRingedSpace) E m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded T ⊤).obj E) m := by
  have : IsIso (⊤ : T.Opens).ι := by rw [← Scheme.topIso_hom]; exact Iso.isIso_hom _
  have ecancel : (Scheme.Modules.pushforward (⊤ : T.Opens).ι).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor (⊤ : T.Opens).ι).mapDerivedCategory.obj E) ≅ E :=
    (Functor.mapDerivedCategoryCompIsoOfCompIso
        (Scheme.Modules.restrictFunctorCompPushforwardIso (⊤ : T.Opens).ι)).app E ≪≫
      (Functor.mapDerivedCategoryId T.Modules).app E
  refine Iff.trans ?_ (isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded E hE
    (isAffineOpen_top T) m)
  refine Iff.trans ?_ (Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff
    (⊤ : T.Opens).ι ((Scheme.Modules.restrictFunctor (⊤ : T.Opens).ι).mapDerivedCategory.obj E) m)
  exact ⟨fun h => RingedSpace.IsPseudoCoherentFrom.of_iso (X := T.toRingedSpace) h ecancel.symm,
    fun h => RingedSpace.IsPseudoCoherentFrom.of_iso (X := T.toRingedSpace) h ecancel⟩

/-- **On one affine scheme, pseudo-coherence on the small étale site is pseudo-coherence of
`RΓ(T, -)`, in a fixed degree.**  Let `T` be an affine scheme in a big étale site, let `E₀` be an
object of `D(𝒪_T)` all of whose cohomology sheaves are quasi-coherent and let `m` be an integer.
Then `ε^*E₀` is `m`-pseudo-coherent on the small étale site of `T` if and only if the complex
`RΓ(T, E₀)` of `Γ(T, 𝒪_T)`-modules is `m`-pseudo-coherent.

This is **Stacks 08HE** in a fixed degree,
`AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule`, followed by
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff` and by
`AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top`.  Each link is a
biconditional, so both directions fall out of the one composite. -/
public theorem isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top
    (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T) [IsAffine T]
    (E₀ : DerivedCategory (SheafOfModules.{u} T.ringCatSheaf))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E₀).IsQuasicoherent)
    (m : ℤ) :
    (smallEtaleRingedSite B T hT).IsPseudoCoherentFrom
        ((SmallEtale.associatedModuleOfSheaf B T hT).mapDerivedCategory.obj E₀) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded T ⊤).obj E₀) m :=
  (SmallEtale.pseudoCoherentIffAssociatedModule B T hT E₀ m).symm.trans
    ((Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff T E₀ m).trans
      (isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top E₀ hE₀ m))

/-- **Stacks 071Q at a scheme, as essential surjectivity of `ε^*` on `D_QCoh`.**  Let `F` be an
object of the derived category of `𝒪`-modules on the small étale site of a scheme `T`, all of
whose cohomology sheaves are quasi-coherent.  Then there is an object `E₀` of `D(𝒪_T)` whose
cohomology sheaves are quasi-coherent together with an isomorphism `ε^*E₀ ≅ F`.

`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence` is **Stacks 071Q**: `ε^*`
is an equivalence from `D_QCoh(𝒪_T)` to `D_QCoh(T_étale, 𝒪)`, both read as the full subcategories
of the unbounded derived categories cut out by quasi-coherence of every cohomology sheaf, and it
carries no hypothesis beyond the two derived-category models.  So
`CategoryTheory.Functor.objObjPreimageIso` at the object `⟨F, hF⟩` of the target subcategory
produces the preimage, and the inclusion of the subcategory carries the isomorphism down to the
ambient derived category — where it is the statement above, the composite of
`CategoryTheory.ObjectProperty.lift` with that inclusion being the plain `ε^*` by definition.

The hypothesis `hF` is `DerivedCategoryB.derivedCategoryB` of
`AlgebraicGeometry.SmallEtale.qcohOnSite`, which unfolds to quasi-coherence of every cohomology
sheaf of `F` on the site; no boundedness and no surjectivity side condition is needed. -/
public theorem exists_derived_associatedModuleOfSheaf_iso (B : BigEtaleSite.{u}) (T : Scheme.{u})
    (hT : B.Contains T)
    (F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)))
    (hF : DerivedCategoryB.derivedCategoryB (SmallEtale.qcohOnSite B T hT) F) :
    ∃ E₀ : DerivedCategory (SheafOfModules.{u} T.ringCatSheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E₀).IsQuasicoherent) ∧
        Nonempty ((SmallEtale.associatedModuleOfSheaf B T hT).mapDerivedCategory.obj E₀ ≅ F) := by
  have := SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1} B T hT
  obtain ⟨E₀, ⟨e₀⟩⟩ : ∃ E₀,
      Nonempty ((SmallEtale.derivedAssociatedModule.{u + 1} B T hT).obj E₀ ≅ ⟨F, hF⟩) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  exact ⟨E₀.obj, E₀.property,
    ⟨(DerivedCategoryB.derivedCategoryB (SmallEtale.qcohOnSite B T hT)).ι.mapIso e₀⟩⟩

/-- **The scheme-side half of the chart dictionary, read at the object the small étale site
carries.**  Let `T` be an affine scheme, let `F` be an object of the derived category of
`𝒪`-modules on its small étale site, and let `E₀` be an object of `D(𝒪_T)` with quasi-coherent
cohomology together with an isomorphism `ε^*E₀ ≅ F`.  Then `F` is `m`-pseudo-coherent on the small
étale site of `T` if and only if the complex `RΓ(T, E₀)` of `Γ(T, 𝒪_T)`-modules is
`m`-pseudo-coherent.

This is `AlgebraicGeometry`
`.isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top`
with the isomorphism absorbed by
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso`, the predicate depending only on the
isomorphism class of its object.  Together with
`AlgebraicGeometry.exists_derived_associatedModuleOfSheaf_iso`, which supplies `E₀` and the
isomorphism from quasi-coherence of `F` alone, this is the whole scheme side of item (iii) of the
display in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean` except for
one thing: the identification of `RΓ(T, E₀)` with derived sections of `F` at the final object of
the small étale site, which is comparison (ii) of that display and is not composed here. -/
public theorem isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top_of_iso
    (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T) [IsAffine T]
    (F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)))
    (E₀ : DerivedCategory (SheafOfModules.{u} T.ringCatSheaf))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E₀).IsQuasicoherent)
    (e : (SmallEtale.associatedModuleOfSheaf B T hT).mapDerivedCategory.obj E₀ ≅ F) (m : ℤ) :
    (smallEtaleRingedSite B T hT).IsPseudoCoherentFrom F m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded T ⊤).obj E₀) m :=
  ⟨fun h =>
      (isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top
        B T hT E₀ hE₀ m).1
        (RingedSite.isPseudoCoherentFrom_of_iso (smallEtaleRingedSite B T hT) m h e),
    fun h =>
      RingedSite.isPseudoCoherentFrom_of_iso (smallEtaleRingedSite B T hT) m
        ((isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top
          B T hT E₀ hE₀ m).2 h) e.symm⟩

end AlgebraicGeometry

end
