module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkPushforwardMate
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingGermUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnitOnKFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforwardUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison

/-!
# The unit square of the two derived stalk comparisons at a germ map

`AlgebraicGeometry.DerivedStalkPushforwardUnitSquareAt` is the statement that
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` is the mate of
`AlgebraicGeometry.derivedPullbackStalkIso` read backwards, under `Li^* ⊣ Ri_*` and
`AlgebraicGeometry.derivedStalkGermAdjunction`.  Its file reduces it, by
`AlgebraicGeometry.derivedStalkPushforwardUnitSquare_of_kFlat`, to the square at
`DerivedCategory.Q` of a K-flat complex, and transposes it, by
`AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_iff`, into a statement about
`derivedPullbackStalkIso` alone.  **This file proves that statement**, and so the unit square
unconditionally.

Underived the square is one application of `CategoryTheory.unit_mateEquiv`:
`Stacks.ModuleSkyscraper.pushStalkMap` is *defined* as the mate of
`Stacks.ModuleSkyscraper.pullbackStalkIso`, which is
`AlgebraicGeometry.map_unit_comp_restrictScalarsStalkPushforwardMap`.  Derived, the two
comparisons are built independently, and the square has to be transported down to that underived
identity across four passages, each a naturality step followed by an inverse which exists
because the complex is K-flat:

1. the derived pullback of `DerivedCategory.Q.obj P` to `DerivedCategory.Q` of the degreewise
   pullback, which is `AlgebraicGeometry.pullbackComparisonOnComplex` and is invertible on a
   K-flat complex by `AlgebraicGeometry.isIso_pullbackComparisonOnComplex_of_kFlat`;
2. and 3. the two derived stalks to `DerivedCategory.Q` of the degreewise stalk complexes, by
   `CategoryTheory.Functor.mapDerivedCategoryFactors`;
4. the unit of `Li^* ⊣ Ri_*`, which the library computes at `DerivedCategory.Qh` of a K-flat
   object of the homotopy category
   (`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_eq_of_isKFlat`)
   and which has therefore to be carried from `DerivedCategory.Qh` to `DerivedCategory.Q` along
   `DerivedCategory.quotientCompQhIso`.

## Main results

* `AlgebraicGeometry.extendScalars_map_unit_comp_counit_comp_pullbackStalkIso_inv`: **the
  underived identity**, in the form the derived chase needs it: derived extension of scalars
  along the germ map of the stalk of the unit followed by the germ map, then the counit of
  `ModuleCat.extendRestrictScalarsAdj` and the stalk formula read backwards, is the identity.
* `AlgebraicGeometry.mapHC_degreewise_glue`: the same, degreewise on cochain complexes.
* `AlgebraicGeometry.unit_comp_derivedPushforwardIsoMapDerivedCategory_of_kFlat`: **the
  `Q`/`Qh` passage for the unit of `Li^* ⊣ Ri_*`.**  On a K-flat complex the unit at
  `DerivedCategory.Q.obj P`, followed by the derived pullback comparison and the two
  factorizations of the derived pushforward, is `DerivedCategory.Q` of the degreewise unit.
* `AlgebraicGeometry.derivedStalk_unit_comp_derivedStalkPushforward`: the same with the derived
  stalk at `i z` applied, read down to `DerivedCategory.Q` of the degreewise mate datum.
* `AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_Q_of_kFlat`: **the unit square at
  `DerivedCategory.Q` of a K-flat complex.**
* `AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_all`: **the unit square at every object
  of `D(𝒪_X)`**, by `AlgebraicGeometry.derivedStalkPushforwardUnitSquare_of_kFlat`.
* `AlgebraicGeometry.derivedStalkDerivedPushforwardIso_eq_mate` and
  `AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit'`: the mate
  identification and its counit half, now unconditional.

## Implementation notes

*Why the transposed form is the one proved.*  `derivedStalkPushforwardUnitSquareAt_iff` removes
the unit of `derivedStalkGermAdjunction`, which the library does not compute below
`DerivedCategory.Q`, and replaces it by that adjunction's counit, which
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` does
compute there.

*Why the transposed form is attacked through `derivedPullbackStalkIso_comp_comparison` rather
than directly.*  `derivedPullbackStalkIso` is `Classical.choose` of a uniqueness statement, so
the only handle on it is the equation characterizing it, which involves its `hom` and not its
`inv`.  Composing the goal with the characterizing equation's right-hand side — invertible
exactly because `P` is K-flat — turns the goal into an equality of two morphisms out of
`derivedPullbackStalkIso` read forwards, and the `inv` disappears.

*Why the declarations are small.*  The terms here sit near the kernel's budget; a single chase
through all four passages times out.  Each passage is its own lemma.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

noncomputable section

universe u

namespace StacksDraft.DerivedStalkUnitSquareChase

variable {C : Type*} [Category C]

/-- A morphism which is the identity, between two others. -/
theorem comp_eq_id_comp {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (e : c ⟶ c) (h : c ⟶ d)
    (he : e = CategoryStruct.id c) : f ≫ g ≫ e ≫ h = f ≫ g ≫ h := by
  rw [he, Category.id_comp]

/-- A trailing morphism which is the identity. -/
theorem comp_eq_of_id {a b : C} (f : a ⟶ b) (e : b ⟶ b) (he : e = CategoryStruct.id b) :
    f ≫ e = f := by
  rw [he, Category.comp_id]

/-- A trailing morphism which is the identity, after three others. -/
theorem comp₄_eq_of_id {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (e : d ⟶ d)
    (he : e = CategoryStruct.id d) : f ≫ g ≫ h ≫ e = f ≫ g ≫ h := by
  rw [he, Category.comp_id]

/-- **The inverse of an isomorphism, composed with a factorization of it.**  If `φ' ≫ φ = 𝟙`
and `φ ≫ t = g`, then `φ' ≫ g = t`. -/
theorem inv_comp_eq_of_hom_comp {a b c : C} (φ : a ⟶ b) (φ' : b ⟶ a) (g : a ⟶ c) (t : b ⟶ c)
    (hφ : φ' ≫ φ = CategoryStruct.id b) (hg : φ ≫ t = g) : φ' ≫ g = t := by
  rw [← hg, ← Category.assoc, hφ, Category.id_comp]

/-- **The chase that carries the unit of `Li^* ⊣ Ri_*` from `Q` down to the degreewise unit.**
Read `η ≫ R₁ ≫ R₂ ≫ R₃ ≫ Φ ≫ Fa` as the derived unit followed by the three factors of the
pullback comparison under `Ri_*`, the comparison of `Ri_*` with its degreewise model and that
model's factorization, and `Qw` as the answer.  The seven hypotheses are, in order: the
naturality of the unit along the passage from `Q` to `Qh`; the unit at `Qh` with the pullback
comparison cancelled; the naturality of the pushforward comparison along the passage back from
`Qh` to `Q`; the derived pushforward's unit against that comparison; the `Q`/`Qh` passage for
the two factorizations of the degreewise pushforward; the naturality of the passage from `Qh` to
`Q`; and its cancellation. -/
theorem unitChase {a b n n₁ n₂ n₃ m l p g : C}
    {η : a ⟶ n} {Rc : n ⟶ n₃} {R₁ : n ⟶ n₁} {R₂ : n₁ ⟶ n₂} {R₃ : n₂ ⟶ n₃} {Φ : n₃ ⟶ m}
    {Fa : m ⟶ l}
    {v : a ⟶ b} {η' : b ⟶ n₁} {u : b ⟶ p} {d : p ⟶ n₂} {Φ' : n₂ ⟶ g} {FR : g ⟶ m}
    {Fi : p ⟶ g} {t : p ⟶ l} {s : b ⟶ a} {Qw : a ⟶ l}
    (h₀ : Rc = R₁ ≫ R₂ ≫ R₃)
    (h₃ : η ≫ R₁ = v ≫ η') (h₄ : η' ≫ R₂ = u ≫ d) (h₅ : R₃ ≫ Φ = Φ' ≫ FR)
    (h₆ : d ≫ Φ' = Fi) (h₇ : Fi ≫ FR ≫ Fa = t) (h₈ : u ≫ t = s ≫ Qw)
    (h₉ : v ≫ s = CategoryStruct.id a) :
    η ≫ Rc ≫ Φ ≫ Fa = Qw := by
  rw [h₀, Category.assoc, Category.assoc, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅,
    reassoc_of% h₆, h₇, h₈, reassoc_of% h₉]

/-- A functor applied to a composite of three morphisms. -/
theorem map_comp₃ {D : Type*} [Category D] (F : C ⥤ D) {w x y z : C} (α : w ⟶ x) (β : x ⟶ y)
    (γ : y ⟶ z) : F.map (α ≫ β ≫ γ) = F.map α ≫ F.map β ≫ F.map γ := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- **The tail of the germ square at a complex.**  Read `ΦC` as the component of the derived
stalk of a derived pushforward at `DerivedCategory.Q` of a complex, `G₁ ≫ ⋯ ≫ G₆` as its
six-factor expansion, and `RU₂ ≫ RF` as the two factorizations of
`(−)_z ⋙ restrictScalars (i^♯_z)` read forwards.  The last two factors of the expansion are the
inverses of those two factorizations, so they cancel and four factors are left. -/
theorem phiTail {a₁' a₃ a₄ a₅ y₁ y₂ y₃ : C} {ΦC : a₁' ⟶ a₃} {RU₂ : a₃ ⟶ a₄} {RF : a₄ ⟶ a₅}
    {G₁ : a₁' ⟶ y₁} {G₂ : y₁ ⟶ y₂} {G₃ : y₂ ⟶ y₃} {G₄ : y₃ ⟶ a₅} {G₅ : a₅ ⟶ a₄} {G₆ : a₄ ⟶ a₃}
    (k₂ : ΦC = G₁ ≫ G₂ ≫ G₃ ≫ G₄ ≫ G₅ ≫ G₆)
    (k₃ : G₆ ≫ RU₂ = CategoryStruct.id a₄) (k₄ : G₅ ≫ RF = CategoryStruct.id a₅) :
    ΦC ≫ RU₂ ≫ RF = G₁ ≫ G₂ ≫ G₃ ≫ G₄ := by
  rw [k₂, Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    reassoc_of% k₃, k₄, Category.comp_id]

/-- **The chase that reads the transposed unit square down to a degreewise map.**  Read
`Stη ≫ Φ ≫ RU₁ ≫ RU₂ ≫ RF` as the derived stalk at `i z` of the unit of `Li^* ⊣ Ri_*`, the
germ square at the derived pullback, and the three passages to `DerivedCategory.Q` of the
degreewise stalk complexes, and `SF ≫ Qv` as the answer.  The five hypotheses are, in order:
the naturality of the germ square along the pullback comparison; the tail of the germ square at
a complex (`phiTail`); the derived stalk of the `Q`/`Qh` passage for the unit, merged into one
localized morphism; the naturality of the stalk factorization at `i z` along the degreewise
unit; and the merge of the last two localized morphisms. -/
theorem stalkChase {a₀ a₁ a₁' a₂ a₃ a₄ a₅ b₀ y₁ y₂ y₃ : C}
    {Stη : a₀ ⟶ a₁} {Φ : a₁ ⟶ a₂} {RU₁ : a₂ ⟶ a₃} {RU₂ : a₃ ⟶ a₄} {RF : a₄ ⟶ a₅}
    {StRc : a₁ ⟶ a₁'} {ΦC : a₁' ⟶ a₃}
    {G₁ : a₁' ⟶ y₁} {G₂ : y₁ ⟶ y₂} {G₃ : y₂ ⟶ y₃} {G₄ : y₃ ⟶ a₅}
    {StQw : a₀ ⟶ y₂} {SF : a₀ ⟶ b₀} {Qsw : b₀ ⟶ y₃} {Qv : b₀ ⟶ a₅}
    (k₁ : Φ ≫ RU₁ = StRc ≫ ΦC) (k₂ : ΦC ≫ RU₂ ≫ RF = G₁ ≫ G₂ ≫ G₃ ≫ G₄)
    (k₅ : Stη ≫ StRc ≫ G₁ ≫ G₂ = StQw) (k₆ : StQw ≫ G₃ = SF ≫ Qsw) (k₇ : Qsw ≫ G₄ = Qv) :
    Stη ≫ Φ ≫ RU₁ ≫ RU₂ ≫ RF = SF ≫ Qv := by
  rw [reassoc_of% k₁, k₂, reassoc_of% k₅, reassoc_of% k₆, k₇]

/-- A functor applied to a four-fold composite which is known to be a two-fold one. -/
theorem map_comp₄_of_eq {D : Type*} [Category D] (F : C ⥤ D) {a b c d e x : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) (p : a ⟶ x) (q : x ⟶ e)
    (hyp : f ≫ g ≫ h ≫ k = p ≫ q) :
    F.map f ≫ F.map g ≫ F.map h ≫ F.map k = F.map p ≫ F.map q := by
  rw [StacksDraft.DerivedStalkComponentChase.map_comp₄, hyp,
    CategoryTheory.Functor.map_comp]

/-- Cancelling an invertible morphism on the right. -/
theorem eq_of_comp_right_eq {a b c : C} {f g : a ⟶ b} (m : b ⟶ c) (hm : IsIso m)
    (h : f ≫ m = g ≫ m) : f = g := by
  exact (cancel_mono m).1 h

/-- **The chase that transposes the unit square across the germ adjunction.**  Read
`(TA ≫ εA) ≫ u₁ ≫ u₂ ≫ Qψ` as the transposed left-hand side composed with the right-hand side
of the equation characterizing `derivedPullbackStalkIso`, and `TSF ≫ gP` as that equation's
left-hand side after the isomorphism.  The six hypotheses are, in order: the naturality of the
counit of the germ adjunction along the two stalk passages; the counit at `DerivedCategory.Q` of
a complex; the derived extension of scalars of the stalk chase; the naturality of the comparison
of derived extension of scalars with its degreewise model; and the underived identity. -/
theorem counitChase {t₀ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ q₁ s₀ : C}
    {TA : t₀ ⟶ t₁} {εA : t₁ ⟶ a₁} {u₁ : a₁ ⟶ a₂} {u₂ : a₂ ⟶ a₃} {Qψ : a₃ ⟶ a₄}
    {T₁ : t₁ ⟶ t₂} {εA' : t₂ ⟶ a₂} {T₂ : t₂ ⟶ t₃} {εB : t₃ ⟶ a₃} {T₃ : t₃ ⟶ t₄}
    {gA : t₄ ⟶ q₁} {Qε : q₁ ⟶ a₃} {TSF : t₀ ⟶ s₀} {TQv : s₀ ⟶ t₄} {gP : s₀ ⟶ a₄}
    {QEv : a₄ ⟶ q₁}
    (m₁ : εA ≫ u₁ = T₁ ≫ εA') (m₂ : εA' ≫ u₂ = T₂ ≫ εB) (m₃ : εB = T₃ ≫ gA ≫ Qε)
    (m₄ : TA ≫ T₁ ≫ T₂ ≫ T₃ = TSF ≫ TQv) (m₅ : TQv ≫ gA = gP ≫ QEv)
    (m₆ : QEv ≫ Qε ≫ Qψ = CategoryStruct.id a₄) :
    (TA ≫ εA) ≫ u₁ ≫ u₂ ≫ Qψ = TSF ≫ gP := by
  rw [Category.assoc, reassoc_of% m₁, reassoc_of% m₂, m₃, Category.assoc, Category.assoc,
    reassoc_of% m₄, reassoc_of% m₅, m₆, Category.comp_id]

end StacksDraft.DerivedStalkUnitSquareChase

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section Underived

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z)

/-- **The underived unit identity at the germ map**, in the form the derived chase needs it.

Derived extension of scalars along `i^♯_z` of the stalk at `i z` of the unit of `i^* ⊣ i_*`
followed by the germ map `Stacks.ModuleSkyscraper.pushStalkMap`, then the counit of
`ModuleCat.extendRestrictScalarsAdj` and the stalk formula of Tag 0098 read backwards, is the
identity.

This is `Stacks.ModuleSkyscraper.map_unit_comp_pushStalkMap` — the unit half of the mate
correspondence for `pushStalkMap` — transposed across
`ModuleCat.extendRestrictScalarsAdj (i^♯_z)`: the unit disappears into the left triangle
identity and the stalk formula cancels against its inverse. -/
theorem extendScalars_map_unit_comp_counit_comp_pullbackStalkIso_inv (N : X.Modules) :
    (ModuleCat.extendScalars.{u, u, u} (i.stalkMap z).hom).map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (i z)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N) ≫
            (Stacks.ModuleSkyscraper.pushStalkMap i z).app
              ((Scheme.Modules.pullback i).obj N)) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (i.stalkMap z).hom).counit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).obj
            ((Scheme.Modules.pullback i).obj N)) ≫
        (Stacks.ModuleSkyscraper.pullbackStalkIso i z).inv.app N =
      CategoryStruct.id _ := by
  rw [Stacks.ModuleSkyscraper.map_unit_comp_pushStalkMap, Functor.map_comp, Category.assoc,
    reassoc_of% ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (i.stalkMap z).hom).counit_naturality
        ((Stacks.ModuleSkyscraper.pullbackStalkIso i z).hom.app N))]
  simp

/-- **The underived unit identity, degreewise on cochain complexes.**  This is
`AlgebraicGeometry.extendScalars_map_unit_comp_counit_comp_pullbackStalkIso_inv` in each degree:
every ingredient of that identity is applied degreewise here, and a morphism of complexes is the
identity as soon as each of its components is. -/
theorem mapHC_degreewise_glue (P : CochainComplex X.Modules ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} (i.stalkMap z).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (i z)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              ((NatTrans.mapHomologicalComplex
                (Scheme.Modules.pullbackPushforwardAdjunction i).unit
                  (ComplexShape.up ℤ)).app P) ≫
            (NatTrans.mapHomologicalComplex (Stacks.ModuleSkyscraper.pushStalkMap i z)
                (ComplexShape.up ℤ)).app
              (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (i.stalkMap z).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).counit.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((Scheme.Modules.pullback i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
        (NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso i z).symm
          (ComplexShape.up ℤ)).hom.app P =
      CategoryStruct.id _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have hc : (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (i.stalkMap z).hom).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((Scheme.Modules.pullback i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))).f n =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (i.stalkMap z).hom).counit.app
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).obj
          ((Scheme.Modules.pullback i).obj (P.X n))) := rfl
  simpa [hc] using extendScalars_map_unit_comp_counit_comp_pullbackStalkIso_inv i z (P.X n)

end Underived

section QhPassage

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

omit [AlgebraicGeometry.IsClosedImmersion i] in
/-- The unfolding of `pullbackComparisonOnComplex`. -/
theorem pullbackComparisonOnComplex_eq_of_schemes (P : CochainComplex X.Modules ℤ) :
    pullbackComparisonOnComplex i P =
      (derivedPullback i.toLRSHom.toShHom).map
          ((DerivedCategory.quotientCompQhIso X.Modules).inv.app P) ≫
        (derivedPullbackComparison i.toLRSHom.toShHom).app
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj P) ≫
          (DerivedCategory.quotientCompQhIso Z.Modules).hom.app
            (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (rfl : pullbackComparisonOnComplex i P = _ ≫ _ ≫ DerivedCategory.Qh.map
      (CategoryStruct.id _) ≫ _).trans
    (StacksDraft.DerivedStalkUnitSquareChase.comp_eq_id_comp _ _ _ _
      (CategoryTheory.Functor.map_id _ _))

omit [AlgebraicGeometry.IsClosedImmersion i] in
/-- The unit of `Li^* ⊣ Ri_*` at `Qh` of a K-flat object, with the pullback comparison
cancelled against the inverse that K-flatness supplies. -/
theorem unit_app_Qh_comp_map_derivedPullbackComparison_of_isKFlat
    (M : HomotopyCategory X.Modules (ComplexShape.up ℤ))
    (hM : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat X.toSheafedSpace M) :
    (derivedAdjunction i.toLRSHom.toShHom).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward i.toLRSHom.toShHom).map
          ((derivedPullbackComparison i.toLRSHom.toShHom).app M) =
      DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app M) ≫
        (derivedPushforwardUnit i.toLRSHom.toShHom).app
          (((modulePullback i.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) := by
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_isKFlat
    i.toLRSHom.toShHom M hM
  rw [derivedAdjunction_unit_app_eq_of_isKFlat i.toLRSHom.toShHom M hM, Category.assoc]
  exact StacksDraft.DerivedStalkUnitSquareChase.comp_eq_of_id _ _
    (StacksDraft.DerivedStalkComponentChase.map_inv_hom _ _ _
      (IsIso.inv_hom_id ((derivedPullbackComparison i.toLRSHom.toShHom).app M)))

/-- **The `Q`/`Qh` passage for the derived pushforward's two factorizations.** -/
theorem derivedPushforwardFactorsh_inv_app_quotient_comp
    (C : CochainComplex Z.Modules ℤ) :
    (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient Z.Modules (ComplexShape.up ℤ)).obj C) ≫
        (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory.map
            ((DerivedCategory.quotientCompQhIso Z.Modules).hom.app C) ≫
          (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app C =
      (DerivedCategory.quotientCompQhIso X.Modules).hom.app
        (((modulePushforward i.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) :=
  StacksDraft.DerivedStalkUnitSquareChase.inv_comp_eq_of_hom_comp _ _ _ _
    (Iso.inv_hom_id_app _ _)
    (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso
      (modulePushforward i.toLRSHom.toShHom) C)

/-- **The `Q`/`Qh` passage for the unit of `Li^* ⊣ Ri_*` on a K-flat complex.** -/
theorem unit_app_Q_comp_pullbackComparison_comp_pushforwardFactors_of_kFlat
    (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P) :
    (derivedAdjunction i.toLRSHom.toShHom).unit.app (DerivedCategory.Q.obj P) ≫
        (derivedPushforward i.toLRSHom.toShHom).map (pullbackComparisonOnComplex i P) ≫
          (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app
              (DerivedCategory.Q.obj (((Scheme.Modules.pullback i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction
          (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom)
            (ComplexShape.up ℤ)).unit.app P) :=
  StacksDraft.DerivedStalkUnitSquareChase.unitChase
    ((congrArg (fun k => (derivedPushforward i.toLRSHom.toShHom).map k)
        (pullbackComparisonOnComplex_eq_of_schemes i P)).trans
      (StacksDraft.DerivedStalkUnitSquareChase.map_comp₃ _ _ _ _))
    ((derivedAdjunction i.toLRSHom.toShHom).unit.naturality
      ((DerivedCategory.quotientCompQhIso X.Modules).inv.app P)).symm
    (unit_app_Qh_comp_map_derivedPullbackComparison_of_isKFlat i _ hP)
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
      i.toLRSHom.toShHom).hom.naturality
        ((DerivedCategory.quotientCompQhIso Z.Modules).hom.app
          (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (Stacks.ClosedImmersion.derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory
      i.toLRSHom.toShHom _)
    (derivedPushforwardFactorsh_inv_app_quotient_comp i _)
    ((DerivedCategory.quotientCompQhIso X.Modules).hom.naturality _)
    (Iso.inv_hom_id_app (DerivedCategory.quotientCompQhIso X.Modules) P)

end QhPassage

section StalkPassage

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- **The transposed unit square, read down to `DerivedCategory.Q` of a degreewise map.** -/
theorem derivedStalk_unit_comp_germSquare_comp_factors_of_kFlat
    (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P) :
    (AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
            ((derivedAdjunction i.toLRSHom.toShHom).unit.app (DerivedCategory.Q.obj P)) ≫
          (derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
              ((derivedPullback i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
            (ModuleCat.restrictScalars.{u, u, u}
                  (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
                ((AlgebraicGeometry.derivedStalkFunctor z).map
                  (pullbackComparisonOnComplex i P)) ≫
              (ModuleCat.restrictScalars.{u, u, u}
                    (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
                  ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    z).mapDerivedCategoryFactors.hom.app
                      (((Scheme.Modules.pullback i).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj P)) ≫
                (ModuleCat.restrictScalars.{u, u, u}
                    (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategoryFactors.hom.app
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj
                      (((Scheme.Modules.pullback i).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj P)) =
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X
          (i.toLRSHom.toShHom.hom.base z)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
                  (i.toLRSHom.toShHom.hom.base z)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              ((Adjunction.mapHomologicalComplexAdjunction
                (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom)
                  (ComplexShape.up ℤ)).unit.app P) ≫
            (NatTrans.mapHomologicalComplex (Stacks.ModuleSkyscraper.pushStalkMap i z)
                (ComplexShape.up ℤ)).app
              (((Scheme.Modules.pullback i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) :=
  StacksDraft.DerivedStalkUnitSquareChase.stalkChase
    ((derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.naturality
      (pullbackComparisonOnComplex i P)).symm
    (StacksDraft.DerivedStalkUnitSquareChase.phiTail
      (derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q i z _)
      (StacksDraft.DerivedStalkComponentChase.map_inv_hom _ _ _
        (Iso.inv_hom_id_app (Stacks.ModuleSkyscraper.modulesStalkFunctor Z
          z).mapDerivedCategoryFactors _))
      (Iso.inv_hom_id_app (ModuleCat.restrictScalars.{u, u, u}
        (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategoryFactors _))
    ((StacksDraft.DerivedStalkComponentChase.map_comp₄ _ _ _ _ _).trans
      (congrArg
        (fun k => (AlgebraicGeometry.derivedStalkFunctor
          (i.toLRSHom.toShHom.hom.base z)).map k)
        (unit_app_Q_comp_pullbackComparison_comp_pushforwardFactors_of_kFlat i P hP)))
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
      (i.toLRSHom.toShHom.hom.base z)).mapDerivedCategoryFactors.hom.naturality _)
    (StacksDraft.DerivedStalkComponentChase.map_comp₂ DerivedCategory.Q _ _).symm

end StalkPassage

section Assembly

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- The left-derived universal property of the germ model, re-seated at the spelling of
`AlgebraicGeometry.germAlpha`, as `derivedStalkGermAdjunction` uses it. -/
local instance isLeftDerived_germAlpha_unitSquare :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor.IsLeftDerivedFunctor
      (germAlpha i z)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (ToType (X.presheaf.stalk (i z))))
        (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).isLeftDerived

/-- **The unit square of the two derived comparisons, at `DerivedCategory.Q` of a K-flat
complex.**  This is the one obligation `derivedStalkPushforwardUnitSquare_of_kFlat` leaves. -/
theorem derivedStalkPushforwardUnitSquareAt_Q_of_kFlat
    (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P) :
    DerivedStalkPushforwardUnitSquareAt i z (DerivedCategory.Q.obj P) := by
  rw [derivedStalkPushforwardUnitSquareAt_iff]
  have : IsIso ((derivedStalkFunctor z).map (pullbackComparisonOnComplex i P)) :=
    ((derivedStalkFunctor z).mapIso
      (@asIso _ _ _ _ _ (isIso_pullbackComparisonOnComplex_of_kFlat i P hP))).isIso_hom
  have g₂ : IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
      z).mapDerivedCategoryFactors.hom.app
        (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    inferInstance
  have g₃ : IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso i z).symm
        (ComplexShape.up ℤ)).hom.app P)) :=
    inferInstance
  have hmain := StacksDraft.DerivedStalkUnitSquareChase.counitChase
    ((derivedStalkGermAdjunction i z).counit.naturality
      ((derivedStalkFunctor z).map (pullbackComparisonOnComplex i P))).symm
    ((derivedStalkGermAdjunction i z).counit.naturality
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapDerivedCategoryFactors.hom.app
        (((Scheme.Modules.pullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).symm
    (derivedExtensionScalarsAdjunction_counit_app_eq.{u, u, u} (i.stalkMap z).hom
      (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor (germAlpha i z) _)
    (StacksDraft.DerivedStalkUnitSquareChase.map_comp₄_of_eq
      (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor _ _ _ _ _ _
      ((Category.assoc _ _ _).trans
        (derivedStalk_unit_comp_germSquare_comp_factors_of_kFlat i z P hP)))
    ((germAlpha i z).naturality _)
    ((StacksDraft.DerivedStalkUnitSquareChase.map_comp₃ DerivedCategory.Q _ _ _).symm.trans
      ((congrArg (fun k => DerivedCategory.Q.map k) (mapHC_degreewise_glue i z P)).trans
        (CategoryTheory.Functor.map_id _ _)))
  refine StacksDraft.DerivedStalkUnitSquareChase.eq_of_comp_right_eq _ ?_
    ((StacksDraft.DerivedStalkUnitSquareChase.inv_comp_eq_of_hom_comp _ _ _ _
      (Iso.inv_hom_id_app _ _) (derivedPullbackStalkIso_comp_comparison i z P)).trans hmain.symm)
  exact IsIso.comp_isIso' ‹_› (IsIso.comp_isIso' g₂ g₃)

/-- **The unit square of the two derived comparisons at the germ map, at every object of
`D(𝒪_X)`.**  Every object is isomorphic to `DerivedCategory.Q` of a K-flat complex, so
`AlgebraicGeometry.derivedStalkPushforwardUnitSquare_of_kFlat` extends
`AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_Q_of_kFlat` to all of them. -/
theorem derivedStalkPushforwardUnitSquareAt_all (K : DerivedCategory X.Modules) :
    DerivedStalkPushforwardUnitSquareAt i z K :=
  derivedStalkPushforwardUnitSquare_of_kFlat i z
    (fun P hP => derivedStalkPushforwardUnitSquareAt_Q_of_kFlat i z P hP) K

/-- **The mate identification, unconditionally.**
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` is the mate of
`AlgebraicGeometry.derivedPullbackStalkIso` read backwards, under `Li^* ⊣ Ri_*` and
`AlgebraicGeometry.derivedStalkGermAdjunction`. -/
theorem derivedStalkDerivedPushforwardIso_eq_mate :
    mateEquiv (derivedAdjunction i.toLRSHom.toShHom) (derivedStalkGermAdjunction i z)
        (TwoSquare.mk _ _ _ _ (AlgebraicGeometry.derivedPullbackStalkIso i z).inv) =
      TwoSquare.mk _ _ _ _
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom :=
  derivedStalkDerivedPushforwardIso_eq_mateEquiv i z
    (derivedStalkPushforwardUnitSquareAt_all i z)

/-- **The counit half of the mate correspondence, unconditionally.**  This is the derived form of
`Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`. -/
theorem extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes
    (K : DerivedCategory Z.Modules) :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor.map
          ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
            K) ≫
        (derivedStalkGermAdjunction i z).counit.app
          ((AlgebraicGeometry.derivedStalkFunctor z).obj K) =
      (AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app
          ((derivedPushforward i.toLRSHom.toShHom).obj K) ≫
        (AlgebraicGeometry.derivedStalkFunctor z).map
          ((derivedAdjunction i.toLRSHom.toShHom).counit.app K) :=
  extendScalars_map_derivedStalkPushforward_comp_counit i z
    (derivedStalkPushforwardUnitSquareAt_all i z) K

end Assembly

end AlgebraicGeometry

end

end
