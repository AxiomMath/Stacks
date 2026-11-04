module

public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Composites of arbitrary models of derived extension of scalars, at independent universes

Let `f : R →+* M` and `g : M →+* B` be homomorphisms of commutative rings, the three rings
living in three *independent* universes, and let `(F, α)` and `(G, β)` be arbitrary models of
derived extension of scalars along `f` and along `g` — that is, total left derived functors of
degreewise extension of scalars, with no further structure.  Then `F ⋙ G` is a model of derived
extension of scalars along `g ∘ f`.

`StacksDraft.DerivedExtensionScalarsComp` and
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` record this only for
the *chosen* models `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` and
only when the three rings share one universe.  Both restrictions are inessential and both are
removed here; what is used downstream is
`StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso`, which compares the two composites
around a commuting square of ring homomorphisms

```
  R ---→ M
  |      |
  v      v
  M' --→ B
```

for four independently chosen models.  That is the shape of the two ways of base changing a
derived category of modules along the two edges of `R → A`, `R → R'`, `A → A ⊗_R R'`,
`R' → A ⊗_R R'`, where the four rings occupy the universes `uR`, `uA`, `uR'` and
`max uA uR'` and no two of them can be collapsed.

## Main definitions

* `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` — the composition
  isomorphism for degreewise extension of scalars, at three independent ring universes.
* `StacksDraft.DerivedExtensionScalarsModelComp.extensionOfScalarsComplexCompIso` — the same
  on cochain complexes, followed by localization.
* `StacksDraft.DerivedExtensionScalarsModelComp.compComparison` — the comparison from the
  composite of two models to degreewise extension of scalars along the composite ring map.
* `StacksDraft.DerivedExtensionScalarsModelComp.compModelIso` — the composite of two models is
  the chosen model of derived extension of scalars along the composite.
* `StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso` — **the square**: the two
  composites around a commuting square of ring maps are isomorphic.

## Main results

* `StacksDraft.DerivedExtensionScalarsModelComp.isIso_comparison_app_of_kFlat` — the comparison
  of *any* model is invertible at a K-flat complex.  This is a field of
  `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` for the chosen model; for
  an arbitrary one it follows by uniqueness of left derived functors.
* `StacksDraft.DerivedExtensionScalarsModelComp.isIso_compComparison_app_of_kFlat` — hence the
  composite comparison is invertible at a K-flat complex, because degreewise extension of scalars
  preserves K-flatness ([stacks 06Y1]).
* `StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison` — the
  characterizing equation of `compModelIso`.
* `StacksDraft.DerivedExtensionScalarsModelComp.isLeftDerivedFunctor_comp` — the composite of
  two models *is* a model: it is a total left derived functor of degreewise extension of scalars
  along the composite ring map.
* `StacksDraft.DerivedExtensionScalarsModelComp.comp_hom_ext` — hence two morphisms into the
  composite agree as soon as they agree against the composite comparison at every cochain
  complex.  This is how a morphism assembled from units and counits is identified with
  `modelSquareIso`.
* `StacksDraft.DerivedExtensionScalarsModelComp.unit_extendScalarsComp` and its primed form — the
  defining equation of `extendScalarsComp` read against the units of the two extension/restriction
  adjunctions.  On elements both sides send `m` to `1 ⊗ (1 ⊗ m)`, but the equation is stated
  between morphisms: at three independent ring universes that nested pure tensor has no `Module`
  instance to elaborate against, and the morphism form is what a degreewise argument on a complex
  needs.
* `StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso_hom_app_comp_comparison` — the
  characterizing equation of `modelSquareIso`: the two composite comparisons agree across it.

## Implementation notes

`StacksDraft.DerivedExtensionScalarsModelComp.isLeftDerivedFunctor_comp` is a theorem and not an
instance: the comparison it is stated for carries the equality `g ∘ f = h` of ring maps, which no
instance search can guess.  It is not used to *construct* the comparison isomorphism either, and
uniqueness of left derived functors is not invoked on the composite.  Instead the canonical
morphism to the chosen model
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` is produced by the universal
property of that model and shown invertible, exactly as in
`StacksDraft.DerivedExtensionScalarsComp`: that keeps the characterizing equation available as a
`CategoryTheory.Functor.leftDerived_fac_app`, which is the form a diagram chase needs, and it
avoids transporting an `IsLeftDerivedFunctor` instance along the equality of ring maps
`g ∘ f = g' ∘ f'`.  The equality is absorbed instead by one `CategoryTheory.eqToHom` in
`StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq`.

The three ring universes are `u₁`, `u₂`, `u₃` and the common module universe is
`max v u₁ u₂ u₃`, which is the only way to say that it contains all three.  The derived
categories are instance arguments, as they are in
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

namespace StacksDraft.DerivedExtensionScalarsModelComp

universe u₁ u₂ u₃ v w₁ w₂ w₃

/-- Extension of scalars along a bare ring homomorphism is additive, at a module universe
independent of the two ring universes.  Mathlib derives additivity through the adjunction, whose
module universe is written `max u₂ w`; the universes here are three independent ones and
`max v u₁ u₂ u₃` is not of that shape to the universe unifier, so the instance is supplied
directly. -/
local instance extendScalarsAdditive {S : Type u₁} {T : Type u₂} [CommRing S] [CommRing T]
    (f : S →+* T) : (ModuleCat.extendScalars.{u₁, u₂, v} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

section Model

variable {R : Type u₁} {A : Type u₂} [CommRing R] [CommRing A]
  [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁ u₂} R)]
  [HasDerivedCategory.{w₂} (ModuleCat.{max v u₁ u₂} A)]

/-- **The comparison of any model of derived extension of scalars is invertible at a K-flat
complex.**  For the model chosen by
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` this is the field
`comparison_isIso_of_kFlat`; an arbitrary model receives a canonical morphism to the chosen one
which is invertible by the universal property, and the factorization of
`CategoryTheory.Functor.leftDerived_fac_app` transports the invertibility. -/
theorem isIso_comparison_app_of_kFlat (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v u₁ u₂} R) ⥤
      DerivedCategory (ModuleCat.{max v u₁ u₂} A))
    (α : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{u₁, v, u₂, w₂} f)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂} R) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{max v u₁ u₂} R) ℤ)
    (hP : CochainComplex.KFlat.{u₁, max v u₂} P) :
    IsIso (α.app P) := by
  let T := totalDerivedExtensionScalars.{u₁, u₂, v, w₁, w₂} f
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂} R) (ComplexShape.up ℤ)
  have hT : IsIso (T.comparison.app P) := T.comparison_isIso_of_kFlat P hP
  have hτ : IsIso (T.functor.leftDerivedLift T.comparison W F α) :=
    (T.functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift T.comparison W F α).1 inferInstance
  rw [← T.functor.leftDerived_fac_app T.comparison W F α P]
  infer_instance

end Model

section Resolution

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁} R)]

/-- A natural transformation out of a derived category of modules which is invertible at the
class of every K-flat complex is invertible: every object receives a quasi-isomorphism from a
K-flat complex ([stacks 06Y4]), and naturality transports invertibility along it. -/
theorem isIso_of_isIso_app_kFlat {D : Type*} [Category* D]
    {F G : DerivedCategory (ModuleCat.{max v u₁} R) ⥤ D} (t : F ⟶ G)
    (ht : ∀ M : CochainComplex (ModuleCat.{max v u₁} R) ℤ, CochainComplex.KFlat.{u₁, v} M →
      IsIso (t.app (DerivedCategory.Q.obj M))) :
    IsIso t := by
  have key (X : DerivedCategory (ModuleCat.{max v u₁} R)) : IsIso (t.app X) := by
    obtain ⟨P, p, hP, -, hp, -⟩ :=
      CochainComplex.KFlat.exists_kFlat_resolution.{u₁, v} (DerivedCategory.Q.objPreimage X)
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    have := ht P hP
    have h : IsIso (t.app (DerivedCategory.Q.obj P) ≫ G.map e.hom) := inferInstance
    rw [← t.naturality e.hom] at h
    exact (isIso_comp_left_iff _ _).mp h
  exact NatIso.isIso_of_isIso_app _

end Resolution

section Comp

variable {R : Type u₁} {A : Type u₂} {B : Type u₃} [CommRing R] [CommRing A] [CommRing B]

/-- **Degreewise extension of scalars composes, at three independent ring universes.**
Extending scalars along `f : R →+* A` and then along `g : A →+* B` is extending them along
`g ∘ f`.  `ModuleCat.extendScalarsComp` says this only for three rings in one universe; the
isomorphism is obtained here in the same way, by conjugating the composition isomorphism of the
right adjoints across the two adjunctions, which are available at independent universes. -/
def extendScalarsComp (f : R →+* A) (g : A →+* B) :
    ModuleCat.extendScalars.{u₁, u₃, max v u₁ u₂ u₃} (g.comp f) ≅
      ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f ⋙
        ModuleCat.extendScalars.{u₂, u₃, max v u₁ u₂ u₃} g :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₂} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₂, u₃} g))
    (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₃} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp f g).symm

/-- **The unit normal form of the composition isomorphism.**  The unit of extension of scalars
along `g ∘ f`, followed by the restriction of
`StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp`, is the unit of the composite
adjunction, followed by the composition isomorphism of the two restrictions.  On elements both
sides send `m` to `1 ⊗ (1 ⊗ m)`.

This *is* the defining property of the isomorphism: it is the conjugate of
`ModuleCat.restrictScalarsComp` across the two adjunctions, and
`CategoryTheory.unit_conjugateEquiv_symm` is that definition read at a module.  Stating it as an
equation of morphisms rather than on elements keeps it usable degreewise on a complex, where the
pure tensors of the three mixed universes are not available as a single expression. -/
theorem unit_extendScalarsComp (f : R →+* A) (g : A →+* B)
    (M : ModuleCat.{max v u₁ u₂ u₃} R) :
    (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₃} (g.comp f)).unit.app M ≫
        (ModuleCat.restrictScalars.{max v u₁ u₂ u₃} (g.comp f)).map
          ((extendScalarsComp.{u₁, u₂, u₃, v} f g).hom.app M) =
      ((ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₂} f).comp
          (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₂, u₃} g)).unit.app M ≫
        (ModuleCat.restrictScalarsComp.{max v u₁ u₂ u₃} f g).inv.app
          ((ModuleCat.extendScalars.{u₂, u₃, max v u₁ u₂ u₃} g).obj
            ((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).obj M)) :=
  (unit_conjugateEquiv_symm
    ((ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₂} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₂, u₃} g))
    (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₃} (g.comp f))
    (ModuleCat.restrictScalarsComp.{max v u₁ u₂ u₃} f g).symm.hom M).symm

/-- `StacksDraft.DerivedExtensionScalarsModelComp.unit_extendScalarsComp` with the unit of the
composite adjunction expanded into the two units.  This is the form a diagram chase meets, and it
is not reachable from the folded form by `rw`: the two spellings of the object
`restrict f (restrict g (extend g (extend f M)))` — one as a composite functor applied to `M`,
one as a nest of applications — are definitionally equal but not syntactically, and keyed matching
does not cross that.  `CategoryTheory.Adjunction.comp_unit_app` is therefore applied through
`congrArg`. -/
theorem unit_extendScalarsComp' (f : R →+* A) (g : A →+* B)
    (M : ModuleCat.{max v u₁ u₂ u₃} R) :
    (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₂} f).unit.app M ≫
        (ModuleCat.restrictScalars.{max v u₁ u₂ u₃} f).map
            ((ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₂, u₃} g).unit.app
              ((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).obj M)) ≫
          (ModuleCat.restrictScalarsComp.{max v u₁ u₂ u₃} f g).inv.app
            ((ModuleCat.extendScalars.{u₂, u₃, max v u₁ u₂ u₃} g).obj
              ((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj.{max v u₁ u₂ u₃, u₁, u₃} (g.comp f)).unit.app M ≫
        (ModuleCat.restrictScalars.{max v u₁ u₂ u₃} (g.comp f)).map
          ((extendScalarsComp.{u₁, u₂, u₃, v} f g).hom.app M) := by
  refine Eq.trans ?_ (unit_extendScalarsComp.{u₁, u₂, u₃, v} f g M).symm
  rw [← Category.assoc]
  exact congrArg
    (fun (z : M ⟶ _) => z ≫ (ModuleCat.restrictScalarsComp.{max v u₁ u₂ u₃} f g).inv.app
      ((ModuleCat.extendScalars.{u₂, u₃, max v u₁ u₂ u₃} g).obj
        ((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).obj M)))
    (Adjunction.comp_unit_app _ _ M).symm

variable [HasDerivedCategory.{w₃} (ModuleCat.{max v u₁ u₂ u₃} B)]

/-- `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` applied degreewise and
localized: degreewise extension of scalars along `f`, then degreewise extension of scalars along
`g` followed by localization, is degreewise extension of scalars along `g ∘ f` followed by
localization. -/
def extensionOfScalarsComplexCompIso (f : R →+* A) (g : A →+* B) :
    (ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplexGeneral.{u₂, max v u₁, u₃, w₃} g ≅
      extensionOfScalarsComplexGeneral.{u₁, max v u₂, u₃, w₃} (g.comp f) :=
  isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (extendScalarsComp.{u₁, u₂, u₃, v} f g).symm
      (ComplexShape.up ℤ)) DerivedCategory.Q

variable [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁ u₂ u₃} R)]
  [HasDerivedCategory.{w₂} (ModuleCat.{max v u₁ u₂ u₃} A)]

variable (f : R →+* A) (g : A →+* B)
  (F : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} R) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A))
  (α : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{u₁, max v u₂ u₃, u₂, w₂} f)
  (G : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} B))
  (β : DerivedCategory.Q ⋙ G ⟶ extensionOfScalarsComplexGeneral.{u₂, max v u₁, u₃, w₃} g)

/-- **The comparison from the composite of two models.**  The comparison of the first model,
then the second model applied to it, then the degreewise composition isomorphism: a natural
transformation from `Q ⋙ (F ⋙ G)` to degreewise extension of scalars along `g ∘ f`. -/
def compComparison :
    DerivedCategory.Q ⋙ (F ⋙ G) ⟶
      extensionOfScalarsComplexGeneral.{u₁, max v u₂, u₃, w₃} (g.comp f) :=
  whiskerRight α G ≫
    whiskerLeft ((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).mapHomologicalComplex
      (ComplexShape.up ℤ)) β ≫
    (extensionOfScalarsComplexCompIso.{u₁, u₂, u₃, v, w₃} f g).hom

/-- The value of the composite comparison at a cochain complex. -/
theorem compComparison_app (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ) :
    (compComparison f g F α G β).app P =
      G.map (α.app P) ≫
        β.app (((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
        (extensionOfScalarsComplexCompIso.{u₁, u₂, u₃, v, w₃} f g).hom.app P :=
  rfl

variable [hFld : F.IsLeftDerivedFunctor α
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ))]
  [hGld : G.IsLeftDerivedFunctor β
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} A) (ComplexShape.up ℤ))]

/-- **The composite comparison is invertible at a K-flat complex.**  Both comparisons are
invertible there by
`StacksDraft.DerivedExtensionScalarsModelComp.isIso_comparison_app_of_kFlat` — the second one
because degreewise extension of scalars along `f` carries K-flat complexes to K-flat complexes
([stacks 06Y1]) — and the degreewise composition isomorphism is invertible everywhere. -/
theorem isIso_compComparison_app_of_kFlat
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ)
    (hP : CochainComplex.KFlat.{u₁, max v u₂ u₃} P) :
    IsIso ((compComparison f g F α G β).app P) := by
  have h1 : IsIso (α.app P) :=
    @isIso_comparison_app_of_kFlat.{u₁, u₂, max v u₃, w₁, w₂} R A _ _ _ _ f F α hFld P hP
  have h2 : IsIso (β.app (((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    @isIso_comparison_app_of_kFlat.{u₂, u₃, max v u₁, w₂, w₃} A B _ _ _ _ g G β hGld _
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u₁, u₂, max v u₃} f P hP)
  rw [compComparison_app]
  exact IsIso.comp_isIso' (G.mapIso (asIso (α.app P))).isIso_hom
    (IsIso.comp_isIso' h2 inferInstance)

/-- The composite comparison, retargeted along an equality `g ∘ f = h` of ring homomorphisms.
This is the one place the commutation of the square enters; nothing else has to be transported
along it. -/
def compComparisonOfEq (h : R →+* B) (hfg : g.comp f = h) :
    DerivedCategory.Q ⋙ (F ⋙ G) ⟶
      extensionOfScalarsComplexGeneral.{u₁, max v u₂, u₃, w₃} h :=
  compComparison f g F α G β ≫
    eqToHom (congrArg (fun φ => extensionOfScalarsComplexGeneral.{u₁, max v u₂, u₃, w₃} φ) hfg)

/-- The retargeted comparison is invertible at a K-flat complex. -/
theorem isIso_compComparisonOfEq_app_of_kFlat (h : R →+* B) (hfg : g.comp f = h)
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ)
    (hP : CochainComplex.KFlat.{u₁, max v u₂ u₃} P) :
    IsIso ((compComparisonOfEq f g F α G β h hfg).app P) := by
  subst hfg
  simpa [compComparisonOfEq] using isIso_compComparison_app_of_kFlat f g F α G β P hP

/-- The canonical morphism from the composite of two models to the chosen model of derived
extension of scalars along `h = g ∘ f`, from the universal property of the latter. -/
def compHom (h : R →+* B) (hfg : g.comp f = h) :
    F ⋙ G ⟶ (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).functor :=
  (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).functor.leftDerivedLift
    (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ)) _
    (compComparisonOfEq f g F α G β h hfg)

omit hFld hGld in
/-- **The defining equation of the canonical morphism.**  Composing it with the comparison of
the chosen model returns the composite comparison, at every cochain complex. -/
theorem compHom_app_comp_comparison (h : R →+* B) (hfg : g.comp f = h)
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ) :
    (compHom f g F α G β h hfg).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison.app P =
      (compComparisonOfEq f g F α G β h hfg).app P :=
  (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).functor.leftDerived_fac_app
    (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ)) _
    (compComparisonOfEq f g F α G β h hfg) P

/-- **The canonical morphism is invertible.**  At the class of a K-flat complex both the
composite comparison and the comparison of the chosen model are invertible, so the defining
equation makes the morphism invertible there; an arbitrary object receives a quasi-isomorphism
from a K-flat complex. -/
instance isIso_compHom (h : R →+* B) (hfg : g.comp f = h) :
    IsIso (compHom f g F α G β h hfg) := by
  refine isIso_of_isIso_app_kFlat.{u₁, max v u₂ u₃, w₁} _ fun P hP => ?_
  have hT : IsIso ((totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison.app P) :=
    (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison_isIso_of_kFlat P hP
  have hcomp : IsIso ((compHom f g F α G β h hfg).app (DerivedCategory.Q.obj P) ≫
      (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison.app P) := by
    rw [compHom_app_comp_comparison]
    exact isIso_compComparisonOfEq_app_of_kFlat f g F α G β h hfg P hP
  exact IsIso.of_isIso_comp_right _
    ((totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison.app P)

/-- **The composite of two models of derived extension of scalars is a model of derived
extension of scalars along the composite ring map.** -/
def compModelIso (h : R →+* B) (hfg : g.comp f = h) :
    F ⋙ G ≅ (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).functor :=
  asIso (compHom f g F α G β h hfg)

/-- The characterizing equation of
`StacksDraft.DerivedExtensionScalarsModelComp.compModelIso`. -/
theorem compModelIso_hom_app_comp_comparison (h : R →+* B) (hfg : g.comp f = h)
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ) :
    (compModelIso f g F α G β h hfg).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison.app P =
      (compComparisonOfEq f g F α G β h hfg).app P :=
  compHom_app_comp_comparison f g F α G β h hfg P

/-- **The composite of two models is itself a model.**  `F ⋙ G`, with the composite comparison
retargeted along `g ∘ f = h`, is a total left derived functor of degreewise extension of scalars
along `h`.  This is `StacksDraft.DerivedExtensionScalarsModelComp.isIso_compHom` read through
`CategoryTheory.Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift`. -/
theorem isLeftDerivedFunctor_comp (h : R →+* B) (hfg : g.comp f = h) :
    (F ⋙ G).IsLeftDerivedFunctor (compComparisonOfEq f g F α G β h hfg)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ)) :=
  (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).functor
    (totalDerivedExtensionScalars.{u₁, u₃, max v u₂, w₁, w₃} h).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ))
    (F ⋙ G) (compComparisonOfEq f g F α G β h hfg)).2
    (isIso_compHom f g F α G β h hfg)

/-- **Two morphisms into the composite of two models agree as soon as they agree against the
composite comparison, at every cochain complex.**  The composite is a total left derived functor
by `StacksDraft.DerivedExtensionScalarsModelComp.isLeftDerivedFunctor_comp`, so
`CategoryTheory.Functor.leftDerived_ext` applies.

This is the tool for identifying a morphism built from units and counits of adjunctions with the
square isomorphism `StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso`. -/
theorem comp_hom_ext (h : R →+* B) (hfg : g.comp f = h)
    (H : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} R) ⥤
      DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} B))
    (γ₁ γ₂ : H ⟶ F ⋙ G)
    (hγ : ∀ P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ,
      γ₁.app (DerivedCategory.Q.obj P) ≫ (compComparisonOfEq f g F α G β h hfg).app P =
        γ₂.app (DerivedCategory.Q.obj P) ≫ (compComparisonOfEq f g F α G β h hfg).app P) :
    γ₁ = γ₂ := by
  have := isLeftDerivedFunctor_comp f g F α G β h hfg
  refine Functor.leftDerived_ext (F ⋙ G) (compComparisonOfEq f g F α G β h hfg)
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ))
    H γ₁ γ₂ ?_
  ext P
  exact hγ P

end Comp

section Square

variable {R : Type u₁} {A : Type u₂} {A' : Type u₃} {B : Type max u₂ u₃}
  [CommRing R] [CommRing A] [CommRing A'] [CommRing B]
  [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁ u₂ u₃} R)]
  [HasDerivedCategory.{w₂} (ModuleCat.{max v u₁ u₂ u₃} A)]
  [HasDerivedCategory.{w₃} (ModuleCat.{max v u₁ u₂ u₃} A')]
  [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁ u₂ u₃} B)]

variable (f : R →+* A) (g : A →+* B) (f' : R →+* A') (g' : A' →+* B)
  (h : R →+* B) (hfg : g.comp f = h) (hfg' : g'.comp f' = h)
  (F : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} R) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A))
  (α : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{u₁, max v u₂ u₃, u₂, w₂} f)
  (G : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} B))
  (β : DerivedCategory.Q ⋙ G ⟶
    extensionOfScalarsComplexGeneral.{u₂, max v u₁ u₃, max u₂ u₃, w₁} g)
  (F' : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} R) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A'))
  (α' : DerivedCategory.Q ⋙ F' ⟶ extensionOfScalarsComplexGeneral.{u₁, max v u₂ u₃, u₃, w₃} f')
  (G' : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A') ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} B))
  (β' : DerivedCategory.Q ⋙ G' ⟶
    extensionOfScalarsComplexGeneral.{u₃, max v u₁ u₂, max u₂ u₃, w₁} g')

variable [hF : F.IsLeftDerivedFunctor α
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ))]
  [hG : G.IsLeftDerivedFunctor β
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} A) (ComplexShape.up ℤ))]
  [hF' : F'.IsLeftDerivedFunctor α'
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} R) (ComplexShape.up ℤ))]
  [hG' : G'.IsLeftDerivedFunctor β'
    (HomologicalComplex.quasiIso (ModuleCat.{max v u₁ u₂ u₃} A') (ComplexShape.up ℤ))]

include hfg hfg' hF hG hF' hG' in
/-- **The two composites around a commuting square of ring homomorphisms agree**, for four
arbitrary models of derived extension of scalars at four rings in four independent universes.

Both composites are models of derived extension of scalars along the common composite `h`, by
`StacksDraft.DerivedExtensionScalarsModelComp.compModelIso`, so each is canonically isomorphic to
the chosen model there.

This is the isomorphism `F ⋙ G ≅ F' ⋙ G'` of the square

```
  R ---→ A
  |      |
  v      v
  A' --→ B
```

read at arbitrary models; for `A ⊗_R R'` in the lower right corner the four universes are
`uR`, `uA`, `uR'` and `max uA uR'`, and no two of them collapse. -/
def modelSquareIso : F ⋙ G ≅ F' ⋙ G' :=
  compModelIso.{u₁, u₂, max u₂ u₃, max v u₃, w₁, w₂, w₁} f g F α G β h hfg ≪≫
    (compModelIso.{u₁, u₃, max u₂ u₃, max v u₂, w₁, w₃, w₁} f' g' F' α' G' β' h hfg').symm

include hfg hfg' hF hG hF' hG' in
/-- **The characterizing equation of the square isomorphism.**  Composing it with the composite
comparison of the second pair of models returns the composite comparison of the first, at every
cochain complex; the chosen model of derived extension of scalars along `h` has been eliminated.
This is what makes the isomorphism usable in a diagram chase. -/
theorem modelSquareIso_hom_app_comp_comparison
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ) :
    (modelSquareIso f g f' g' h hfg hfg' F α G β F' α' G' β').hom.app
          (DerivedCategory.Q.obj P) ≫
        (compComparisonOfEq.{u₁, u₃, max u₂ u₃, max v u₂, w₁, w₃, w₁}
          f' g' F' α' G' β' h hfg').app P =
      (compComparisonOfEq.{u₁, u₂, max u₂ u₃, max v u₃, w₁, w₂, w₁}
        f g F α G β h hfg).app P := by
  rw [← compModelIso_hom_app_comp_comparison.{u₁, u₃, max u₂ u₃, max v u₂, w₁, w₃, w₁}
      f' g' F' α' G' β' h hfg' P,
    ← compModelIso_hom_app_comp_comparison.{u₁, u₂, max u₂ u₃, max v u₃, w₁, w₂, w₁}
      f g F α G β h hfg P]
  dsimp only [modelSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, ← Category.assoc
    ((compModelIso.{u₁, u₃, max u₂ u₃, max v u₂, w₁, w₃, w₁}
      f' g' F' α' G' β' h hfg').inv.app _), ← NatTrans.comp_app,
    Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]

end Square

end StacksDraft.DerivedExtensionScalarsModelComp

end
