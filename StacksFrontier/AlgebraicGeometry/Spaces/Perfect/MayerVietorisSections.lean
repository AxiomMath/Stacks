module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Mayer–Vietoris for the cohomology of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V`.  Stacks 0CRS says that every object `E` of `D(𝒪_X)` sits in a
distinguished triangle

`RΓ(X,E) ⟶ RΓ(U,E) ⊕ RΓ(V,E) ⟶ RΓ(U ×_X V,E) ⟶ RΓ(X,E)[1]`

and hence in a long exact cohomology sequence

`… ⟶ H^n(X,E) ⟶ H^n(U,E) ⊕ H^n(V,E) ⟶ H^n(U ×_X V,E) ⟶ H^{n+1}(X,E) ⟶ …`

Both are deduced here, together with their functoriality in `E`, from the abstract
Mayer–Vietoris triangle of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative` taken at the additive
functor of global sections.  The relative statement, Stacks 08JK, is in that module.  All three
clauses hold with no hypothesis beyond the square.

## Main results

The three declarations registered as **Stacks 0CRS**, one per clause of the tag, each taking no
hypothesis beyond the elementary distinguished square and the four right derived functors with
the comparisons that present `RΓ`:

* `AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris_unconditional`: the
  distinguished triangle.
* `AlgebraicGeometry.Space.exists_homologySequence_exact_edsSectionsMayerVietoris_unconditional`:
  the long exact cohomology sequence.
* `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`:
  the *functoriality in `E`* of both — the five maps are the components of natural
  transformations of functors on `D(𝒪_X)`.

Unregistered:

* `AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris`,
  `AlgebraicGeometry.Space.exists_homologySequence_exact_edsSectionsMayerVietoris` and
  `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris`: the same
  three clauses granted part (1) of Stacks 08GW for an arbitrary module.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris_of_shriek` and
  `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek`:
  the same clauses taking the three extension-by-zero adjunctions as given data.
* `CategoryTheory.PushforwardMayerVietoris.exists_natTrans_mem_distTriang_mapMayerVietoris` and
  `CategoryTheory.PushforwardMayerVietoris`
  `.exists_natTrans_mem_distTriang_mapMayerVietoris_of_injective`: the abstract form of the
  functorial statement, for an arbitrary additive functor out of an abelian category admitting
  termwise injective K-injective resolutions, with the Mayer–Vietoris sequence demanded at
  every object and at the injective objects only.

## Implementation notes

*Global sections at a termwise injective complex.*  `Γ(X, -)` is only left exact, so it cannot be
applied to the Mayer–Vietoris short exact sequence of Stacks 08GW part (1) degreewise at an
arbitrary complex.  It can be applied at a *termwise injective* complex, because there the
sequence splits; that is the content of
`CategoryTheory.PushforwardMayerVietoris.shortExact_map_mayerVietoris_of_injective`, and Stacks
079P supplies a resolution that is K-injective and termwise injective at once
(`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_injective_modules`).

*What `RΓ(U, E)` is here.*  The three outer terms are the right derived functors of
`Γ(X, -) ∘ Φ_Y` with `Φ_Y = j_{Y,*}((-)|_Y)`, in that factored form.  That
`Γ(X, j_{Y,*}N) = Γ(Y, N)` is the defining property of the direct image — the adjunction
`(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU read on hom-groups out of the free module of rank one, which
is `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso` for a morphism of ringed topoi.
That comparison is not transported to `AlgebraicGeometry.Space.modulePushforward` here.

*`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off.*  It is a global
instance `Abelian (SheafOfModules.{max u v r w} O)` whose universe is a `max` of four
variables, so instance search for `Abelian (AlgebraicGeometry.Space.Modules.{u, u} …)` against
it leaves a stuck universe constraint and even the binder
`[HasDerivedCategory.{u + 1} (Modules.{u, u} …)]` fails to elaborate.  The erasure is
section-scoped, and the `Abelian` instance actually used is the one that
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian` provides at the pinned universes.

*Functoriality.*  The first four maps are produced by the universal property of the right
derived functor, `CategoryTheory.Functor.rightDerivedNatTrans`.  The connecting map is the one
`DerivedCategory.triangleOfSESδ` attaches to the Mayer–Vietoris sequence at a chosen termwise
injective K-injective resolution `I(E)` of each object, transported along the chosen isomorphism
`Q(I(E)) ≅ E`.  It is natural because that connecting map is natural in the short exact
sequence (`DerivedCategory.triangleOfSESδ_naturality`), and every morphism `Q(I(E)) ⟶ Q(I(E'))`
of the derived category is `Q` of a morphism of complexes, which is the fullness half of
Stacks 070K at a K-injective target
(`CategoryTheory.PushforwardMayerVietoris.exists_eq_Q_map_of_isKInjective`).

*The Mayer–Vietoris sequence at injective modules.*  The sequence
`0 ⟶ M ⟶ j_{U,*}M|_U ⊕ j_{V,*}M|_V ⟶ j_{P,*}M|_P ⟶ 0` of Stacks 08GW part (1) enters only at
the terms of the termwise injective K-injective resolution of `E` that Stacks 079P supplies, and
at an injective module it is a theorem,
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`: part (1) of
**Stacks 08GV**, the extension-by-zero sequence `0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`
(`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`), has a monomorphism as its first
map, and a monomorphism into an injective module admits an extension, which transposes across
the adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)` to a section
(`CategoryTheory.PushforwardMayerVietoris.epi_conjugate_of_injective`).  At a general module the
surjectivity on the right is the étale-local vanishing of an obstruction in
`Ext¹_{𝒪_X}(𝒪_X, F) = H¹(X, F)` (Stacks 01FW); it is not used.

## References

* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.PushforwardMayerVietoris

/-! ### Functoriality of the Mayer–Vietoris triangle in the object of `D(A)` -/

section Functorial

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]

/-- The image under a functor `G` of a natural map `𝟭 ⟶ Φ`, as a natural map `G ⟶ Φ ⋙ G`. -/
@[simps]
def mapUnit {Φ : A ⥤ A} (η : 𝟭 A ⟶ Φ) (G : A ⥤ C) : G ⟶ Φ ⋙ G where
  app M := G.map (η.app M)
  naturality _ _ f := by
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (η.naturality f)

/-- `mapUnitCochainMap G η K` is the component at `K` of `mapUnit η G` applied degreewise. -/
lemma mapUnitCochainMap_eq (G : A ⥤ C) [G.Additive] {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ)
    (K : CochainComplex A ℤ) :
    mapUnitCochainMap G η K =
      (NatTrans.mapHomologicalComplex (mapUnit η G) (ComplexShape.up ℤ)).app K := by
  ext n
  rfl

section KInjective

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]
  (Ψ : A ⥤ C) [Ψ.Additive] (R : DerivedCategory A ⥤ DerivedCategory C)
  (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)

/-- **Stacks 070K, in the form that is natural in the complex.**  A right derived functor of
`Ψ` is computed on a K-injective complex `I` by `Ψ` itself, and the comparison is the composite
of `α` at `I` with the two structural isomorphisms relating `DerivedCategory.Q` to
`DerivedCategory.Qh`. -/
def kinjIso (I : CochainComplex A ℤ)
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    DerivedCategory.Q.obj ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      R.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso C).symm.app
      ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
    DerivedCategory.Qh.mapIso
      ((Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm.app I) ≪≫
    @asIso _ _ _ _ (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) hI ≪≫
    R.mapIso ((DerivedCategory.quotientCompQhIso A).app I)

/-- The forward map of `kinjIso`, written out as a composite. -/
@[simp]
lemma kinjIso_hom (I : CochainComplex A ℤ)
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    (kinjIso Ψ R α I hI).hom =
      (DerivedCategory.quotientCompQhIso C).inv.app
          ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
            ((Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I) ≫
          α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
            R.map ((DerivedCategory.quotientCompQhIso A).hom.app I) :=
  rfl

/-- The comparison `kinjIso` is natural in the complex: it intertwines `Ψ` and `R` applied to a
morphism `g : I ⟶ J`. -/
lemma kinjIso_hom_naturality {I J : CochainComplex A ℤ}
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hJ : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)))
    (g : I ⟶ J) :
    DerivedCategory.Q.map ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (kinjIso Ψ R α J hJ).hom =
      (kinjIso Ψ R α I hI).hom ≫ R.map (DerivedCategory.Q.map g) := by
  have h2 : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
      (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app J =
      (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I ≫
        (Ψ.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) :=
    (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.naturality g
  have h3 : DerivedCategory.Qh.map ((Ψ.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g)) ≫
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J) =
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
        R.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g)) :=
    α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g)
  simp only [kinjIso_hom]
  rw [reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map g)),
    ← Functor.map_comp_assoc, h2, Functor.map_comp_assoc, reassoc_of% h3,
    ← R.map_comp, DerivedCategory.quotientCompQhIso_hom_naturality, R.map_comp]
  simp only [Category.assoc]

/-- Transport of `CategoryTheory.PushforwardMayerVietoris.kinjIso_hom_naturality` along chosen
isomorphisms `Q(I) ≅ E` and `Q(J) ≅ E'`: a morphism `φ : E ⟶ E'` of the derived category and a
morphism `g : I ⟶ J` of complexes representing it are compatible with the comparisons. -/
lemma kinjIso_trans_hom_naturality {I J : CochainComplex A ℤ}
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hJ : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)))
    {E E' : DerivedCategory A} (eI : DerivedCategory.Q.obj I ≅ E)
    (eJ : DerivedCategory.Q.obj J ≅ E') (φ : E ⟶ E') (g : I ⟶ J)
    (hg : DerivedCategory.Q.map g = eI.hom ≫ φ ≫ eJ.inv) :
    DerivedCategory.Q.map ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (kinjIso Ψ R α J hJ ≪≫ R.mapIso eJ).hom =
      (kinjIso Ψ R α I hI ≪≫ R.mapIso eI).hom ≫ R.map φ := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, kinjIso_hom_naturality, Category.assoc, ← R.map_comp, hg,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, R.map_comp,
    Category.assoc]

end KInjective

section Derived

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- **A morphism of the derived category into a K-injective complex comes from a morphism of
cochain complexes.**  This is the other half of Stacks 070K. -/
lemma exists_eq_Q_map_of_isKInjective {I J : CochainComplex A ℤ} (hJ : J.IsKInjective)
    (χ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ g : I ⟶ J, DerivedCategory.Q.map g = χ := by
  have := hJ
  obtain ⟨φ, hφ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) J).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app I ≫ χ ≫
      (DerivedCategory.quotientCompQhIso A).inv.app J)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective φ
  refine ⟨g, ?_⟩
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality (C := A) g
  rw [hφ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app I)).mp hnat).symm

omit [HasDerivedCategory A] [HasDerivedCategory C] in
/-- The square relating the two ways of reading a natural transformation of additive functors on
the homotopy category: degreewise on complexes, or through the induced functors. -/
lemma mapHomotopyCategoryFactors_inv_app_comm {Ψ Ψ' : A ⥤ C} [Ψ.Additive] [Ψ'.Additive]
    (n : Ψ ⟶ Ψ') (I : CochainComplex A ℤ) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex n (ComplexShape.up ℤ)).app I) ≫
      (Ψ'.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I =
      (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I ≫
        (NatTrans.mapHomotopyCategory n (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The derived transformation is computed on a K-injective complex by the transformation
itself.**  For `n : Ψ ⟶ Ψ'` a natural transformation of additive functors and `R`, `R'` right
derived functors of `Ψ`, `Ψ'`, the induced transformation `R ⟶ R'` of
`CategoryTheory.Functor.rightDerivedNatTrans` agrees at a K-injective complex, through the
comparisons of `CategoryTheory.PushforwardMayerVietoris.kinjIso`, with `n` applied
degreewise. -/
lemma kinjIso_trans_hom_rightDerivedNatTrans {Ψ Ψ' : A ⥤ C} [Ψ.Additive] [Ψ'.Additive]
    (R R' : DerivedCategory A ⥤ DerivedCategory C)
    (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (α' : Ψ'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R')
    (hR : R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hR' : R'.IsRightDerivedFunctor α' (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (n : Ψ ⟶ Ψ') {I : CochainComplex A ℤ}
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hI' : IsIso (α'.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    {E : DerivedCategory A} (eI : DerivedCategory.Q.obj I ≅ E) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex n (ComplexShape.up ℤ)).app I) ≫
        (kinjIso Ψ' R' α' I hI' ≪≫ R'.mapIso eI).hom =
      (kinjIso Ψ R α I hI ≪≫ R.mapIso eI).hom ≫
        (Functor.rightDerivedNatTrans R R' α α'
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
          (Functor.whiskerRight (NatTrans.mapHomotopyCategory n (ComplexShape.up ℤ))
            DerivedCategory.Qh)).app E := by
  have := hR
  have := hR'
  have hfac := Functor.rightDerivedNatTrans_app R R' α α'
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory n (ComplexShape.up ℤ))
      DerivedCategory.Qh) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)
  have hnat := (Functor.rightDerivedNatTrans R R' α α'
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory n (ComplexShape.up ℤ))
      DerivedCategory.Qh)).naturality eI.hom
  have hnat' := (Functor.rightDerivedNatTrans R R' α α'
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory n (ComplexShape.up ℤ))
      DerivedCategory.Qh)).naturality ((DerivedCategory.quotientCompQhIso A).hom.app I)
  simp only [Iso.trans_hom, Functor.mapIso_hom, kinjIso_hom, Category.assoc]
  rw [reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex n (ComplexShape.up ℤ)).app I)),
    ← Functor.map_comp_assoc, mapHomotopyCategoryFactors_inv_app_comm,
    Functor.map_comp_assoc, hnat, reassoc_of% hnat', reassoc_of% hfac]
  simp only [Functor.whiskerRight_app]

end Derived

section MayerVietoris

variable {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive]

/-- Degreewise reading of the first Mayer–Vietoris map of cochain complexes. -/
lemma eval_map_mvLift (K : CochainComplex A ℤ) (n : ℤ) :
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
        (biprod.lift
          ((NatTrans.mapHomologicalComplex (mapUnit ηU G) (ComplexShape.up ℤ)).app K)
          ((NatTrans.mapHomologicalComplex (mapUnit ηV G) (ComplexShape.up ℤ)).app K)) =
      biprod.lift (G.map (ηU.app (K.X n))) (G.map (ηV.app (K.X n))) ≫
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).biprodIsoOfAdditive
          (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).inv := by
  rw [Iso.eq_comp_inv, Functor.biprodIsoOfAdditive_hom_map_lift]
  rfl

/-- Degreewise reading of the second Mayer–Vietoris map of cochain complexes. -/
lemma eval_map_mvDesc (K : CochainComplex A ℤ) (n : ℤ) :
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).biprodIsoOfAdditive
          (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).inv ≫
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
          (biprod.desc ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
              (ComplexShape.up ℤ)).app K)
            (-((NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
              (ComplexShape.up ℤ)).app K))) =
      biprod.desc (G.map (dU.app (K.X n))) (-(G.map (dV.app (K.X n)))) := by
  rw [Functor.biprodIsoOfAdditive_inv_map_desc,
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_neg]
  rfl

include hzero in
/-- The image under `G` of the Mayer–Vietoris maps, applied degreewise to a cochain complex, is
a complex. -/
lemma zero_mvCochain (K : CochainComplex A ℤ) :
    biprod.lift ((NatTrans.mapHomologicalComplex (mapUnit ηU G) (ComplexShape.up ℤ)).app K)
        ((NatTrans.mapHomologicalComplex (mapUnit ηV G) (ComplexShape.up ℤ)).app K) ≫
      biprod.desc ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
          (ComplexShape.up ℤ)).app K)
        (-((NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
          (ComplexShape.up ℤ)).app K)) = 0 := by
  ext n
  change (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (_ ≫ _) = 0
  rw [Functor.map_comp, eval_map_mvLift ηU ηV G K n, Category.assoc,
    eval_map_mvDesc dU dV G K n, zero_map_mayerVietoris ηU ηV dU dV hzero G (K.X n)]

/-- The Mayer–Vietoris short complex of cochain complexes: the image under `G` of the
Mayer–Vietoris sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`, applied degreewise to a cochain
complex. -/
def mvShortComplex (K : CochainComplex A ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk _ _ (zero_mvCochain ηU ηV dU dV hzero G K)

/-- A Mayer–Vietoris short complex of cochain complexes is short exact once it is so degreewise. -/
private lemma shortExact_mvShortComplex_of_degreewise (K : CochainComplex A ℤ)
    (h : ∀ n, (ShortComplex.mk (biprod.lift (G.map (ηU.app (K.X n))) (G.map (ηV.app (K.X n))))
      (biprod.desc (G.map (dU.app (K.X n))) (-(G.map (dV.app (K.X n)))))
      (zero_map_mayerVietoris ηU ηV dU dV hzero G (K.X n))).ShortExact) :
    (mvShortComplex ηU ηV dU dV hzero G K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  refine ShortComplex.shortExact_of_iso ?_ (h n)
  refine ShortComplex.isoMk (Iso.refl _)
    (((HomologicalComplex.eval C (ComplexShape.up ℤ) n).biprodIsoOfAdditive
      (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm)
    (Iso.refl _) ?_ ?_
  · dsimp only [mvShortComplex, ShortComplex.map_X₁, ShortComplex.map_f, Iso.refl_hom,
      Iso.symm_hom]
    rw [Category.id_comp]
    exact eval_map_mvLift ηU ηV G K n
  · dsimp only [mvShortComplex, ShortComplex.map_X₃, ShortComplex.map_g, Iso.refl_hom,
      Iso.symm_hom]
    rw [Category.comp_id]
    exact eval_map_mvDesc dU dV G K n

include hzero in
/-- **The Mayer–Vietoris short complex of a termwise injective complex is short exact.** -/
lemma shortExact_mvShortComplex
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (K : CochainComplex A ℤ) (hinj : ∀ n, Injective (K.X n)) :
    (mvShortComplex ηU ηV dU dV hzero G K).ShortExact :=
  shortExact_mvShortComplex_of_degreewise ηU ηV dU dV hzero G K fun n =>
    shortExact_map_mayerVietoris_of_injective ηU ηV dU dV hzero G hMV (K.X n) (hinj n)

include hzero in
/-- **The Mayer–Vietoris short complex of a termwise injective complex is short exact**, granted
the Mayer–Vietoris sequence at the injective objects only. -/
lemma shortExact_mvShortComplex_of_injective
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (K : CochainComplex A ℤ) (hinj : ∀ n, Injective (K.X n)) :
    (mvShortComplex ηU ηV dU dV hzero G K).ShortExact :=
  shortExact_mvShortComplex_of_degreewise ηU ηV dU dV hzero G K fun n =>
    shortExact_map_mayerVietoris_at_injective ηU ηV dU dV hzero G (K.X n) (hinj n)
      (hMV (K.X n) (hinj n))

include hzero in
/-- A morphism of cochain complexes induces a morphism of Mayer–Vietoris short complexes. -/
@[simps]
def mvShortComplexMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    mvShortComplex ηU ηV dU dV hzero G K ⟶ mvShortComplex ηU ηV dU dV hzero G L where
  τ₁ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  τ₂ := biprod.map (((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    (((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  τ₃ := ((ΦP ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  comm₁₂ := by
    dsimp only [mvShortComplex]
    refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.map_fst,
        biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc, NatTrans.naturality]
  comm₂₃ := by
    dsimp only [mvShortComplex]
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      simp only [biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.inl_map_assoc, biprod.inr_map_assoc, Preadditive.comp_neg, Preadditive.neg_comp,
        NatTrans.naturality]

end MayerVietoris

section Assembly

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- **Assembling a triangle of natural transformations out of the data at a chosen
resolution.**  Suppose that for every object `E` of `D(A)` a short exact sequence `S E` of
cochain complexes in `C` is given, together with isomorphisms identifying the derived category
objects of its three terms with `R_X E`, `R_U E ⊕ R_V E` and `R_P E` compatibly with four given
natural transformations `a_U`, `a_V`, `b_U`, `b_V`, and suppose that every morphism of `D(A)` is
induced by a morphism of the sequences compatibly with the first and third identifications.
Then the connecting maps of the sequences assemble into a natural transformation
`δ : R_P ⟶ R_X[1]` for which every

`R_X E ⟶ R_U E ⊕ R_V E ⟶ R_P E ⟶ (R_X E)[1]`

is distinguished. -/
lemma exists_natTrans_mem_distTriang_of_resolutions
    {RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C}
    (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
    (S : DerivedCategory A → ShortComplex (CochainComplex C ℤ))
    (hS : ∀ E, (S E).ShortExact)
    (cX : ∀ E, DerivedCategory.Q.obj (S E).X₁ ≅ RX.obj E)
    (c₂ : ∀ E, DerivedCategory.Q.obj (S E).X₂ ≅ RU.obj E ⊞ RV.obj E)
    (cP : ∀ E, DerivedCategory.Q.obj (S E).X₃ ≅ RP.obj E)
    (h₁ : ∀ E, DerivedCategory.Q.map (S E).f ≫ (c₂ E).hom =
      (cX E).hom ≫ biprod.lift (aU.app E) (aV.app E))
    (h₂ : ∀ E, DerivedCategory.Q.map (S E).g ≫ (cP E).hom =
      (c₂ E).hom ≫ biprod.desc (bU.app E) (-(bV.app E)))
    (hmap : ∀ {E E' : DerivedCategory A} (φ : E ⟶ E'), ∃ ψ : S E ⟶ S E',
      (cX E).hom ≫ RX.map φ = DerivedCategory.Q.map ψ.τ₁ ≫ (cX E').hom ∧
        (cP E).hom ≫ RP.map φ = DerivedCategory.Q.map ψ.τ₃ ≫ (cP E').hom) :
    ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A, Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
        distTriang (DerivedCategory C) := by
  refine ⟨⟨fun E => (cP E).inv ≫ DerivedCategory.triangleOfSESδ (hS E) ≫
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (cX E).hom, ?_⟩, fun E => ?_⟩
  · intro E E' φ
    obtain ⟨ψ, hψX, hψP⟩ := hmap φ
    have hδ := DerivedCategory.triangleOfSESδ_naturality (hS E) (hS E') ψ
    dsimp only [Functor.comp_map]
    refine (cancel_epi (cP E).hom).mp ?_
    simp only [Category.assoc]
    rw [reassoc_of% hψP]
    simp only [Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hδ, ← Functor.map_comp, ← hψX, Functor.map_comp]
  · refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (hS E)) _
      (Triangle.isoMk _ _ (cX E).symm (c₂ E).symm (cP E).symm ?_ ?_ ?_)
    · dsimp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Iso.symm_hom,
        DerivedCategory.triangleOfSES]
      rw [Iso.comp_inv_eq, Category.assoc, h₁ E, Iso.inv_hom_id_assoc]
    · dsimp only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Iso.symm_hom,
        DerivedCategory.triangleOfSES]
      rw [Iso.comp_inv_eq, Category.assoc, h₂ E, Iso.inv_hom_id_assoc]
    · dsimp only [Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₃, Iso.symm_hom,
        DerivedCategory.triangleOfSES]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The long exact homology sequence of a natural Mayer–Vietoris triangle.**  A triangle of
natural transformations whose component at each object is distinguished has, at each object and
each `n`, an exact homology sequence; the maps of that sequence are the images under `H^n` of
the components of the natural transformations, so the sequence is functorial exactly as the
triangle is. -/
lemma exists_natTrans_homologySequence_exact_of_exists_natTrans
    {RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C}
    (h : ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
        (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)),
      ∀ E : DerivedCategory A, Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈ distTriang (DerivedCategory C)) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)),
      ∀ E : DerivedCategory A,
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact := by
  obtain ⟨aU, aV, bU, bV, δ, hT⟩ := h
  exact ⟨aU, aV, bU, bV, δ, fun E => ⟨hT E, fun n =>
    Functor.homologySequenceComposableArrows₅_exact _ _ (hT E) n (n + 1) rfl⟩⟩

end Assembly

section Functoriality

variable {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

include hzero in
/-- **The abstract Mayer–Vietoris triangle is functorial in the object of `D(A)`.**

In the situation of
`CategoryTheory.PushforwardMayerVietoris.exists_mem_distTriang_mapMayerVietoris` — additive
endofunctors `Φ_U`, `Φ_V`, `Φ_P` of an abelian category `A` admitting termwise injective
K-injective resolutions, natural transformations `η_U`, `η_V`, `d_U`, `d_V` whose Mayer–Vietoris
sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` is short exact at every object, an additive
functor `G : A ⥤ C`, and right derived functors `R_X`, `R_U`, `R_V`, `R_P` of `G`, `Φ_U ⋙ G`,
`Φ_V ⋙ G`, `Φ_P ⋙ G` — the five maps of the distinguished triangle

`R_X E ⟶ R_U E ⊕ R_V E ⟶ R_P E ⟶ (R_X E)[1]`

are the components of *natural transformations* of functors on `D(A)`, as in Stacks 08JK and
Stacks 0CRS.  The image under `G` of the Mayer–Vietoris sequence is required to be short exact
only at the *injective* objects. -/
theorem exists_natTrans_mem_distTriang_mapMayerVietoris_of_injective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : (ΦU ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : (ΦV ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : (ΦP ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)),
      ∀ E : DerivedCategory A, Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
        distTriang (DerivedCategory C) := by
  have := hRX
  have := hRU
  have := hRV
  have := hRP
  have hres' : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i := by
    intro K
    obtain ⟨J, i, h1, h2, -⟩ := hres K
    exact ⟨J, i, h1, h2⟩
  choose Res hResK hResInj hResNe using
    fun E : DerivedCategory A => exists_isKInjective_injective_representative hres E
  have e : ∀ E : DerivedCategory A, DerivedCategory.Q.obj (Res E) ≅ E :=
    fun E => (hResNe E).some
  have hiso : ∀ (Ψ : A ⥤ C) [Ψ.Additive] (R : DerivedCategory A ⥤ DerivedCategory C)
      (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ R)
      [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
      (J : CochainComplex A ℤ), J.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)) :=
    fun Ψ _ R α _ J hJ =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        (Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres').2
        DerivedCategory.Qh R α J hJ
  have hX := hiso G RX αX
  have hU := hiso (ΦU ⋙ G) RU αU
  have hV := hiso (ΦV ⋙ G) RV αV
  have hP := hiso (ΦP ⋙ G) RP αP
  refine ⟨Functor.rightDerivedNatTrans RX RU αX αU
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory (mapUnit ηU G) (ComplexShape.up ℤ))
        DerivedCategory.Qh),
    Functor.rightDerivedNatTrans RX RV αX αV
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory (mapUnit ηV G) (ComplexShape.up ℤ))
        DerivedCategory.Qh),
    Functor.rightDerivedNatTrans RU RP αU αP
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (Functor.whiskerRight dU G) (ComplexShape.up ℤ))
        DerivedCategory.Qh),
    Functor.rightDerivedNatTrans RV RP αV αP
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (Functor.whiskerRight dV G) (ComplexShape.up ℤ))
        DerivedCategory.Qh), ?_⟩
  refine exists_natTrans_mem_distTriang_of_resolutions _ _ _ _
    (fun E => mvShortComplex ηU ηV dU dV hzero G (Res E))
    (fun E => shortExact_mvShortComplex_of_injective ηU ηV dU dV hzero G hMV (Res E)
      (hResInj E))
    (fun E => kinjIso G RX αX (Res E) (hX _ (hResK E)) ≪≫ RX.mapIso (e E))
    (fun E => DerivedCategory.Q.biprodIsoOfAdditive _ _ ≪≫
      biprod.mapIso (kinjIso (ΦU ⋙ G) RU αU (Res E) (hU _ (hResK E)) ≪≫ RU.mapIso (e E))
        (kinjIso (ΦV ⋙ G) RV αV (Res E) (hV _ (hResK E)) ≪≫ RV.mapIso (e E)))
    (fun E => kinjIso (ΦP ⋙ G) RP αP (Res E) (hP _ (hResK E)) ≪≫ RP.mapIso (e E))
    (fun E => ?_) (fun E => ?_) (fun {E E'} φ => ?_)
  · have cU := kinjIso_trans_hom_rightDerivedNatTrans RX RU αX αU hRX hRU (mapUnit ηU G)
      (hX _ (hResK E)) (hU _ (hResK E)) (e E)
    have cV := kinjIso_trans_hom_rightDerivedNatTrans RX RV αX αV hRX hRV (mapUnit ηV G)
      (hX _ (hResK E)) (hV _ (hResK E)) (e E)
    dsimp only [mvShortComplex, Iso.trans_hom]
    rw [← Category.assoc, Functor.biprodIsoOfAdditive_hom_map_lift, biprod.mapIso_hom]
    refine biprod.hom_ext _ _ ?_ ?_
    · simpa using cU
    · simpa using cV
  · have cU := kinjIso_trans_hom_rightDerivedNatTrans RU RP αU αP hRU hRP
      (Functor.whiskerRight dU G) (hU _ (hResK E)) (hP _ (hResK E)) (e E)
    have cV := kinjIso_trans_hom_rightDerivedNatTrans RV RP αV αP hRV hRP
      (Functor.whiskerRight dV G) (hV _ (hResK E)) (hP _ (hResK E)) (e E)
    dsimp only [mvShortComplex, Iso.trans_hom]
    rw [Category.assoc, biprod.mapIso_hom, biprod.map_desc, ← Iso.inv_comp_eq,
      Functor.biprodIsoOfAdditive_inv_map_desc_assoc, DerivedCategory.Q.map_neg]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simpa using cU
    · simp only [biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.comp_neg,
        Preadditive.neg_comp]
      rw [neg_inj]
      simpa using cV
  · obtain ⟨g, hg⟩ := exists_eq_Q_map_of_isKInjective (hResK E')
      ((e E).hom ≫ φ ≫ (e E').inv)
    refine ⟨mvShortComplexMap ηU ηV dU dV hzero G g, ?_, ?_⟩
    · exact (kinjIso_trans_hom_naturality G RX αX (hX _ (hResK E)) (hX _ (hResK E'))
        (e E) (e E') φ g hg).symm
    · exact (kinjIso_trans_hom_naturality (ΦP ⋙ G) RP αP (hP _ (hResK E)) (hP _ (hResK E'))
        (e E) (e E') φ g hg).symm

include hzero in
/-- **The abstract Mayer–Vietoris triangle is functorial in the object of `D(A)`**, granted the
Mayer–Vietoris sequence at every object: short exactness of
`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` at every object `M`, the form in which Stacks 08GW part (1)
and Stacks 08JK provide it. -/
theorem exists_natTrans_mem_distTriang_mapMayerVietoris
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : (ΦU ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : (ΦV ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : (ΦP ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)),
      ∀ E : DerivedCategory A, Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
        distTriang (DerivedCategory C) :=
  exists_natTrans_mem_distTriang_mapMayerVietoris_of_injective ηU ηV dU dV hzero G hres
    (fun M _ => hMV M) RX RU RV RP αX αU αV αP hRX hRU hRV hRP

end Functoriality

end Functorial

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sections

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} (RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))]

/-- The Mayer–Vietoris distinguished triangle of global sections, granted part (1) of Stacks
08GW at an arbitrary module.

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V`.  Write `Γ(X, -)` for global sections of `𝒪_X`-modules on the
small étale ringed site, `Φ_Y = j_{Y,*}((-)|_Y)` for the three restrict-then-push composites of
the square, and let `RΓ(X, -)`, `RΓ(U, -)`, `RΓ(V, -)`, `RΓ(P, -)` be right derived functors of
`Γ(X, -)`, `Γ(X, -) ∘ Φ_U`, `Γ(X, -) ∘ Φ_V` and `Γ(X, -) ∘ Φ_P`.  Suppose part (1) of Stacks
08GW holds: the sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` is short exact for every sheaf of
`𝒪_X`-modules `M`.  Then every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`.

The three functors `Γ(X, -) ∘ Φ_Y` *are* `Γ(Y, (-)|_Y)`: that `Γ(X, j_{Y,*}N) = Γ(Y, N)` is the
defining property of the direct image, the adjunction `(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU read on
hom-groups out of the free module of rank one.  The identification is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso` for a morphism of ringed topoi; it
is not transported to `AlgebraicGeometry.Space.modulePushforward` here, so the statement is about
the derived functor of `Γ(X, -) ∘ j_{Y,*} ∘ (-)|_Y`, in the factored form.

As in Stacks 08GV part (2) and Stacks 08GW part (2) the five morphisms are existentially
quantified; for the functoriality in `E` of the triangle see
`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`.
-/
theorem exists_mem_distTriang_edsSectionsMayerVietoris
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) :=
  exists_mem_distTriang_mapMayerVietoris ηU ηV dU dV hzero
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2) hMV
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

/-- The Mayer–Vietoris long exact cohomology sequence, granted part (1) of Stacks 08GW at an
arbitrary module.

The distinguished triangle of
`AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris` has an exact homology
sequence, which at each `n` is the six-term exact sequence

`H^n(X,E) ⟶ H^n(U,E) ⊕ H^n(V,E) ⟶ H^n(U ×_X V,E) ⟶ H^{n+1}(X,E) ⟶ H^{n+1}(U,E) ⊕ H^{n+1}(V,E)
⟶ H^{n+1}(U ×_X V,E)`

— the Mayer–Vietoris long exact sequence of the source, since the homology functor is additive
and so carries the biproduct `RΓ(U,E) ⊕ RΓ(V,E)` to `H^n(U,E) ⊕ H^n(V,E)`.  The connecting map
is `CategoryTheory.Functor.homologySequenceδ` of the triangle, and the exactness is Stacks 0152
read through Mathlib's homology sequence of a distinguished triangle. -/
theorem exists_homologySequence_exact_edsSectionsMayerVietoris
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
          0).homologySequenceComposableArrows₅
        (Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ) n (n + 1) rfl).Exact :=
  exists_homologySequence_exact_of_exists_mem_distTriang
    (exists_mem_distTriang_edsSectionsMayerVietoris
      B S hS hsq RX RU RV RP αX αU αV αP hRX hRU hRV hRP ηU ηV dU dV hzero hMV E)

/-- Functoriality in `E` of the Mayer–Vietoris triangle and sequence of global sections, granted
part (1) of Stacks 08GW at an arbitrary module.

In the situation of `AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris`,
the five maps of the Mayer–Vietoris triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`

are the components at `E` of *natural transformations* of functors on `D(𝒪_X)`, and the long
exact cohomology sequence is the homology sequence of that natural triangle.  The first four
transformations are `CategoryTheory.Functor.rightDerivedNatTrans` applied to the units `η_U`,
`η_V` and the comparisons `d_U`, `d_V` whiskered with global sections. -/
theorem exists_natTrans_mem_distTriang_edsSectionsMayerVietoris
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1}
        (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
            0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact :=
  exists_natTrans_homologySequence_exact_of_exists_natTrans
    (exists_natTrans_mem_distTriang_mapMayerVietoris ηU ηV dU dV hzero
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)))
      (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2) hMV
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP)

end Sections

section Unconditional

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} (RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))]

include adjU adjV adjP in
/-- All three clauses of Stacks 0CRS, given a left adjoint of restriction along each of the
three étale morphisms of the square (extension by zero). -/
theorem exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1}
        (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
            0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact :=
  exists_natTrans_homologySequence_exact_of_exists_natTrans
    (exists_natTrans_mem_distTriang_mapMayerVietoris_of_injective
      (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
      (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
        ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
      (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
        ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
      (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
        (edsShriekOpenComparison B S hS hsq adjU adjP)
        (edsShriekEtaleComparison B S hS hsq adjV adjP)
        (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)))
      (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2)
      (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
        adjU adjV adjP M hM)
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP)

include adjU adjV adjP in
/-- The distinguished triangle clause of Stacks 0CRS, given a left adjoint of restriction along
each of the three étale morphisms of the square (extension by zero). -/
theorem exists_mem_distTriang_edsSectionsMayerVietoris_of_shriek
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) :=
  exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
    (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
      (edsShriekOpenComparison B S hS hsq adjU adjP)
      (edsShriekEtaleComparison B S hS hsq adjV adjP)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2)
    (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
      adjU adjV adjP M hM)
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

/-- **Stacks 0CRS, functoriality in `E`, with nothing granted.**

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V`.  Write `Γ(X, -)` for global sections of `𝒪_X`-modules on the
small étale ringed site, `Φ_Y = j_{Y,*}((-)|_Y)` for the three restrict-then-push composites of
the square, and let `RΓ(X, -)`, `RΓ(U, -)`, `RΓ(V, -)`, `RΓ(P, -)` be right derived functors of
`Γ(X, -)`, `Γ(X, -) ∘ Φ_U`, `Γ(X, -) ∘ Φ_V` and `Γ(X, -) ∘ Φ_P`.  Then the five maps of the
Mayer–Vietoris triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`

are the components of *natural transformations* of functors on `D(𝒪_X)`, every component
triangle is distinguished, and its homology sequence is exact at every `n`.  So a morphism
`E ⟶ E'` induces a morphism of the two triangles and of the two long exact sequences.

As in the conditional statements, the three outer terms are the derived functors of
`Γ(X, -) ∘ j_{Y,*} ∘ (-)|_Y` in that factored form; that this is `RΓ(Y, E|_Y)` is the
adjunction of Stacks 03LU, `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, and is
not transported here. -/
@[stacks 0CRS "THIRD CLAUSE: functoriality in E of the distinguished triangle and of its long
exact cohomology sequence. The five maps are components of natural transformations of functors on
D(O_X); no hypothesis beyond the square and the four derived functors presenting RGamma. The
other two clauses are exists_mem_distTriang_edsSectionsMayerVietoris_unconditional and
exists_homologySequence_exact_edsSectionsMayerVietoris_unconditional"]
theorem exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ (aU : RX ⟶ RU) (aV : RX ⟶ RV) (bU : RU ⟶ RP) (bV : RV ⟶ RP)
      (δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1}
        (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) (1 : ℤ)),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
            0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact :=
  exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP

/-- **Stacks 0CRS, the distinguished triangle, with nothing granted.**

In the situation of
`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`,
every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`. -/
@[stacks 0CRS "FIRST CLAUSE: every E of D(O_X) sits in a distinguished triangle
RGamma(X,E) -> RGamma(U,E) (+) RGamma(V,E) -> RGamma(U x_X V,E) -> RGamma(X,E)[1]; no hypothesis
beyond the square and the four derived functors presenting RGamma. The other two clauses are
exists_homologySequence_exact_edsSectionsMayerVietoris_unconditional and
exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional"]
theorem exists_mem_distTriang_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) :=
  exists_mem_distTriang_edsSectionsMayerVietoris_of_shriek B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

/-- **Stacks 0CRS, the long exact cohomology sequence, with nothing granted.**

The distinguished triangle of
`AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris_unconditional` has an
exact homology sequence, which at each `n` is the six-term exact sequence

`H^n(X,E) ⟶ H^n(U,E) ⊕ H^n(V,E) ⟶ H^n(U ×_X V,E) ⟶ H^{n+1}(X,E) ⟶ H^{n+1}(U,E) ⊕ H^{n+1}(V,E)
⟶ H^{n+1}(U ×_X V,E)`

— the Mayer–Vietoris long exact sequence of the source, since the homology functor is additive
and so carries the biproduct `RΓ(U,E) ⊕ RΓ(V,E)` to `H^n(U,E) ⊕ H^n(V,E)`. -/
@[stacks 0CRS "SECOND CLAUSE: every E of D(O_X) sits in a long exact cohomology sequence
... -> H^n(X,E) -> H^n(U,E) (+) H^n(V,E) -> H^n(U x_X V,E) -> H^{n+1}(X,E) -> ...; no hypothesis
beyond the square and the four derived functors presenting RGamma. It is the homology sequence of
the triangle of exists_mem_distTriang_edsSectionsMayerVietoris_unconditional; functoriality is
exists_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional"]
theorem exists_homologySequence_exact_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
          0).homologySequenceComposableArrows₅
        (Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ) n (n + 1) rfl).Exact :=
  exists_homologySequence_exact_of_exists_mem_distTriang
    (exists_mem_distTriang_edsSectionsMayerVietoris_unconditional B S hS hsq
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP E)

end Unconditional

end AlgebraicGeometry.Space

end
