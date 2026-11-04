module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectResolution
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# The total complex of the twists of an injective resolution

Let `Y` be a scheme, `Λ` a ring, not necessarily commutative, `R` a complex of finite free right
`Λ`-modules and `I` a complex of sheaves of `Λ`-modules on the small étale site of `Y`. The twists
`R^p ⊗[Λ] I^q` form a double complex of abelian sheaves, whose total complex `R ⊠ I` has as its
complex of sections over `Y` the total complex `Tot(R ⊗[Λ] I(Y))` of the twists of the sections.
This is the complex of sheaves through which the proof of [Stacks, Tag 03TV] reads the derived
tensor product `N ⊗ᴸ[Λ] RΓ(X_k̄, K)`.

## Main definitions

* `Stacks.SheafTwist.liftComplex`: a complex of right `Λ`-modules with finite free terms, as a
  complex in the full subcategory of finite free modules.
* `Stacks.SheafTwist.twistComplex`: the total complex `R ⊠ I`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe u r v

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ]

section Additive

variable (D' : BalancedDerivedTensoring.{r, v} Λ)

/-- For a finite free right `Λ`-module `X`, the functor `X ⊗[Λ] -` given by the ordinary tensor
product of `D'` is additive. -/
instance ι_comp_ordinary_obj_additive (X : FiniteFree.{v} Λ) :
    ((ObjectProperty.ι (finiteFree.{v} Λ) ⋙ D'.ordinary).obj X).Additive :=
  inferInstanceAs (D'.ordinary.obj X.obj).Additive

/-- The ordinary tensor product of `D'`, restricted to finite free right `Λ`-modules, is additive
in its first variable. -/
instance ι_comp_ordinary_additive :
    (ObjectProperty.ι (finiteFree.{v} Λ) ⋙ D'.ordinary).Additive where
  map_add {X X'} f g := D'.ordinary.map_add (f := f.hom) (g := g.hom)

end Additive

/-- **A complex of right `Λ`-modules with finite free terms, as a complex of finite free
modules.** -/
def liftComplex (R : CochainComplex (ModuleCat.{max (u + 1) r} (MulOpposite Λ)) ℤ)
    (h : ∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p)) :
    CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ where
  X p := ⟨R.X p, h p⟩
  d p q := ObjectProperty.homMk (R.d p q)
  shape p q hpq := ObjectProperty.hom_ext _ (R.shape p q hpq)
  d_comp_d' p q s _ _ := ObjectProperty.hom_ext _ (R.d_comp_d p q s)

/-- The underlying module of the `p`-th term of `liftComplex R h` is the `p`-th term of `R`. -/
@[simp]
lemma liftComplex_X {Λ : Type r} [Ring Λ]
    (R : CochainComplex (ModuleCat.{max (u + 1) r} (MulOpposite Λ)) ℤ)
    (h : ∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p))
    (p : ℤ) : ((liftComplex.{u} R h).X p).obj = R.X p :=
  rfl

variable (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ) (Y : Scheme.{u})

/-- The twist bifunctor preserves zero morphisms in its first variable. -/
instance twist_preservesZeroMorphisms : (twist D Y).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- **The total complex `R ⊠ I` of the twists** of a complex of sheaves of `Λ`-modules by a complex
of finite free right `Λ`-modules with finitely many nonzero terms. -/
abbrev twistComplex (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    [HasMapBifunctor R I (twist D Y) (ComplexShape.up ℤ)] :
    CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) ℤ :=
  mapBifunctor R I (twist D Y) (ComplexShape.up ℤ)

/-! ### Sections over `Y` -/

section Sections


/-- Sections over the terminal object `Y` of sheaves of `Λ`-modules. -/
abbrev moduleSections : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y ⥤
    ModuleCat.{max (u + 1) r} Λ :=
  (sheafSections Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
    (op (Scheme.Etale.mk (𝟙 Y)))

/-- A double complex with only finitely many nonzero columns has, in each total degree, only
finitely many nonzero terms. -/
lemma finite_support_of_columnBounds {A : Type*} [Category* A] [Preadditive A]
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (e c : ℤ)
    (h : ∀ p, p < e ∨ c < p → IsZero (Z.X p)) (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((Z.X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc e c).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hp : ¬ (p < e ∨ c < p) := fun hp =>
    hz (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q) (h p hp))
  exact ⟨p, ⟨by omega, by omega⟩, by simp only [Prod.mk.injEq, true_and]; omega⟩

/-- **The sections over `Y` of the twists of `I` are the twists of the sections of `I`**: the
double complex of abelian groups `(p, q) ↦ Γ(Y, R^p ⊗ I^q)` is, termwise and on the nose, the
double complex `(p, q) ↦ R^p ⊗ Γ(Y, I^q)` read in abelian groups. -/
def sectionsBicomplexIso (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) :
    HomologicalComplex₂.TotalMap.mapBicomplex (Stacks.EtaleSections.sections.{r, u} Y)
        (((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj R |>.obj I) ≅
      HomologicalComplex₂.TotalMap.mapBicomplex
        (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r})
        ((((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙
          D.ordinary).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj R).obj (((moduleSections Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) :=
  Iso.refl _

/-- **The sections over `Y` of `R ⊠ I` are the total complex of the twists of the sections**, read
in abelian groups, when `R` has finitely many nonzero terms. -/
def sectionsTwistComplexIso (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) (e c : ℤ)
    (h : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)]
    [HasMapBifunctor R (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary) (ComplexShape.up ℤ)]
    [(HomologicalComplex₂.TotalMap.mapBicomplex (Stacks.EtaleSections.sections.{r, u} Y)
        (((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj R |>.obj I)).HasTotal (ComplexShape.up ℤ)] :
    ((Stacks.EtaleSections.sections.{r, u} Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twistComplex D Y R I) ≅
      ((forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (mapBifunctor R (((moduleSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
            (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary) (ComplexShape.up ℤ)) :=
  have hK := finite_support_of_columnBounds
    (((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj R |>.obj I) e c (fun p hp =>
        isZero_of_forall_isZero_X fun q => ((twist.{u, r} D Y).map_isZero (h p hp)).obj (I.X q))
  have hK' := finite_support_of_columnBounds
    ((((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙
      D.ordinary).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj R).obj (((moduleSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) e c (fun p hp =>
        isZero_of_forall_isZero_X fun q =>
          ((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary).map_isZero
            (h p hp)).obj _)
  (HomologicalComplex₂.TotalMap.totalIsoOfFinite (Stacks.EtaleSections.sections.{r, u} Y) _
      hK).symm ≪≫
    HomologicalComplex₂.TotalMap.totalIsoOfFinite
      (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r}) _ hK'

end Sections

end Stacks.SheafTwist

end
