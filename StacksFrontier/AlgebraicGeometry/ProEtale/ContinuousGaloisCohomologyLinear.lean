module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ContinuousGaloisCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.Homology.AcyclicResolutionNaturality
public import StacksFrontier.Homology.DerivedLinear

/-!
# The comparison with continuous cohomology is `Λ`-linear

Let `K` be a field with absolute Galois group `G`. The identification
`Hⁱ(Spec(K)_proét, M^∧) ≅ Hⁱ_cont(G, M)` of the pro-étale cohomology of the sheaf attached to a
topological representation with its continuous cohomology is natural in the representation: a
morphism of representations induces a morphism of the standard resolutions
`C(G, M) → C(G, C(G, M)) → ⋯`, hence of the resolutions of the sheaves, and the computation of
right derived functors by acyclic resolutions is natural.

For a commutative ring `Λ`, the action of `λ ∈ Λ` on `Hⁱ(Spec(K)_proét, M^∧)` is that induced by
functoriality from multiplication by `λ` on `M^∧`, and multiplication by `λ` on `M` induces on the
standard resolution, hence on continuous cohomology, multiplication by `λ`. So the
identification is one of `Λ`-modules.

## Main definitions

* `TopRep.resolution'Map`: the morphism of standard resolutions induced by a morphism of
  topological representations.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedAdicSheafModule`: the `Λ`-module
  `Hⁱ(Spec(K)_proét, M^∧)`.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedAdicSheafLinearEquiv`: case (2) of Stacks 09B4, as
  `Λ`-modules.

## Main results

* `AlgebraicGeometry.GaloisSheaf.rightDerivedRepAbSheafIso_hom_naturality`: the comparison is
  natural in the representation.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedAdicSheafIso_hom_smul`: the comparison of case (2)
  intertwines the actions of `Λ`.

## Implementation notes

Pro-étale cohomology is the right derived functor of global sections of abelian sheaves. For a
sheaf of `Λ`-modules `F`, the group `Hⁱ(F)` is a `Λ`-module through the endomorphisms
`Hⁱ(λ • 𝟙 F)`, which is `ModuleCat.mkOfSMul` of the ring map `Λ → End F → End Hⁱ(F)`; the
`Λ`-linearity of the comparison is the statement that it intertwines these endomorphisms with
multiplication by `λ` on continuous cohomology. Continuous cohomology is lifted to the coefficient
universe of the site, as in `rightDerivedAdicSheafIso`.

## References

* [Stacks Project, Tag 09B4](https://stacks.math.columbia.edu/tag/09B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u r w

namespace TopRep

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The morphisms between the terms `C(G, C(G, ⋯ C(G, X)))` of the standard resolutions induced
by a morphism of topological representations. -/
def resolutionXMap {X Y : TopRep k G} (g : X ⟶ Y) : (i : ℕ) → resolutionX X i ⟶ resolutionX Y i
  | 0 => g
  | i + 1 => (coind₁Functor k G).map (resolutionXMap g i)

/-- In degree `0`, `resolutionXMap g` is `g` itself. -/
@[simp]
lemma resolutionXMap_zero {X Y : TopRep k G} (g : X ⟶ Y) : resolutionXMap g 0 = g := rfl

/-- In degree `i + 1`, `resolutionXMap g` is the image of `resolutionXMap g i` under
`coind₁Functor`. -/
lemma resolutionXMap_succ {X Y : TopRep k G} (g : X ⟶ Y) (i : ℕ) :
    resolutionXMap g (i + 1) = (coind₁Functor k G).map (resolutionXMap g i) := rfl

/-- The morphisms `resolutionXMap g` commute with the differentials of the resolutions. -/
@[reassoc]
lemma resolutionXMap_comp_d {X Y : TopRep k G} (g : X ⟶ Y) (i : ℕ) :
    resolutionXMap g i ≫ d Y i = d X i ≫ resolutionXMap g (i + 1) := by
  induction i with
  | zero => exact ((coind₁ι (k := k) (G := G)).naturality g).symm
  | succ i ih =>
    rw [d_succ, d_succ, Preadditive.comp_sub, Preadditive.sub_comp]
    congr 1
    rw [resolutionXMap_succ _ (i + 1), resolutionXMap_succ _ i, ← Functor.map_comp,
      ← Functor.map_comp, ih]
    rfl

/-- The morphism of shifted standard resolutions `C(G, X) → C(G, C(G, X)) → ⋯` induced by a
morphism of topological representations. -/
def resolution'Map {X Y : TopRep k G} (g : X ⟶ Y) : resolution' X ⟶ resolution' Y :=
  CochainComplex.ofHom (fun i ↦ resolutionXMap g (i + 1)) (fun i ↦ by
    dsimp only [resolution']
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact resolutionXMap_comp_d g (i + 1))

/-- The component of `resolution'Map g` in degree `i` is `resolutionXMap g (i + 1)`. -/
@[simp]
lemma resolution'Map_f {X Y : TopRep k G} (g : X ⟶ Y) (i : ℕ) :
    (resolution'Map g).f i = resolutionXMap g (i + 1) :=
  rfl

end TopRep

namespace TopRep

variable {k G : Type*} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Multiplication by a scalar on a representation induces multiplication by that scalar on each
term `resolutionX X i` of its standard resolution. -/
lemma resolutionXMap_smul_id (X : TopRep k G) (c : k) (i : ℕ) :
    resolutionXMap (c • 𝟙 X) i = c • 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [resolutionXMap_succ, ih, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- Multiplication by a scalar on a representation induces multiplication by that scalar on its
standard resolution. -/
lemma resolution'Map_smul_id (X : TopRep k G) (c : k) :
    resolution'Map (c • 𝟙 X) = c • 𝟙 (resolution' X) := by
  ext i : 1
  rw [resolution'Map_f, resolutionXMap_smul_id, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f]

end TopRep

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

section Naturality

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ]

/-- The comparison of homology with the homology of the underlying abelian groups is natural. -/
lemma underlyingAbHomologyIso_hom_naturality {C D : CochainComplex (TopModuleCat.{max u w} Λ) ℕ}
    (φ : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap (((underlyingAb.{u, r, w} Λ).mapHomologicalComplex _).map φ) n ≫
        (underlyingAbHomologyIso.{u, r, w} Λ D n).hom =
      (underlyingAbHomologyIso.{u, r, w} Λ C n).hom ≫
        (underlyingAb.{u, r, w} Λ).map (HomologicalComplex.homologyMap φ n) := by
  have := additive_uliftFunctor.{max (u + 1) r, max u w}
  let F₁ := forget₂ (TopModuleCat.{max u w} Λ) (ModuleCat.{max u w} Λ)
  let F₂ := forget₂ (ModuleCat.{max u w} Λ) AddCommGrpCat.{max u w}
  let F₃ := AddCommGrpCat.uliftFunctor.{max (u + 1) r, max u w}
  let ψ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).map φ
  have h₁ := ShortComplex.mapHomologyIso_hom_naturality ψ F₁
  have h₂ := ShortComplex.mapHomologyIso_hom_naturality (F₁.mapShortComplex.map ψ) F₂
  have h₃ := ShortComplex.mapHomologyIso_hom_naturality
    (F₂.mapShortComplex.map (F₁.mapShortComplex.map ψ)) F₃
  let S := HomologicalComplex.shortComplexFunctor (TopModuleCat.{max u w} Λ) (ComplexShape.up ℕ) n
  change ShortComplex.homologyMap
        (F₃.mapShortComplex.map (F₂.mapShortComplex.map (F₁.mapShortComplex.map ψ))) ≫
      ((F₂.mapShortComplex.obj (F₁.mapShortComplex.obj (S.obj D))).mapHomologyIso F₃).hom ≫
        F₃.map (((F₁.mapShortComplex.obj (S.obj D)).mapHomologyIso F₂).hom ≫
          F₂.map ((S.obj D).mapHomologyIso F₁).hom) =
    (((F₂.mapShortComplex.obj (F₁.mapShortComplex.obj (S.obj C))).mapHomologyIso F₃).hom ≫
        F₃.map (((F₁.mapShortComplex.obj (S.obj C)).mapHomologyIso F₂).hom ≫
          F₂.map ((S.obj C).mapHomologyIso F₁).hom)) ≫
      F₃.map (F₂.map (F₁.map (ShortComplex.homologyMap ψ)))
  rw [reassoc_of% h₃, Category.assoc]
  congr 1
  rw [← F₃.map_comp, ← F₃.map_comp]
  congr 1
  rw [reassoc_of% h₂, Category.assoc, ← F₂.map_comp, ← F₂.map_comp, h₁]

variable [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}]
  [(Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).Additive]

/-- The identification of global sections of the sheafified standard resolution with the
homogeneous cochains is natural. -/
lemma mapSheafResolutionIso_hom_naturality {X Y : TopRep.{max u w} Λ (galoisGroup K)}
    (g : X ⟶ Y) :
    ((Sheaf.Γ (Scheme.ProEt.topology (base K))
      AddCommGrpCat.{max (u + 1) r w}).mapHomologicalComplex _).map
        (((repAbSheaf.{u, r, max u w} Λ).mapHomologicalComplex _).map
          (TopRep.resolution'Map g)) ≫ (mapSheafResolutionIso Y).hom =
      (mapSheafResolutionIso X).hom ≫ ((underlyingAb.{u, r, w} Λ).mapHomologicalComplex _).map
        (((TopRep.invariantsFunctor Λ (galoisGroup K)).mapHomologicalComplex _).map
          (TopRep.resolution'Map g)) := by
  have h₁ := (Functor.mapHomologicalComplexCompIso (ΓRepAbSheafIso.{u, r, w} K)
    (ComplexShape.up ℕ)).hom.naturality (TopRep.resolution'Map g)
  have h₂ := (Functor.mapHomologicalComplexCompIso (Iso.refl
    (TopRep.invariantsFunctor Λ (galoisGroup K) ⋙ underlyingAb.{u, r, w} Λ))
    (ComplexShape.up ℕ)).inv.naturality (TopRep.resolution'Map g)
  rw [Functor.comp_map] at h₁ h₂
  change _ ≫ (Functor.mapHomologicalComplexCompIso (ΓRepAbSheafIso.{u, r, w} K)
      (ComplexShape.up ℕ)).hom.app _ ≫ (Functor.mapHomologicalComplexCompIso (Iso.refl
        (TopRep.invariantsFunctor Λ (galoisGroup K) ⋙ underlyingAb.{u, r, w} Λ))
        (ComplexShape.up ℕ)).inv.app _ =
    ((Functor.mapHomologicalComplexCompIso (ΓRepAbSheafIso.{u, r, w} K)
      (ComplexShape.up ℕ)).hom.app _ ≫ (Functor.mapHomologicalComplexCompIso (Iso.refl
        (TopRep.invariantsFunctor Λ (galoisGroup K) ⋙ underlyingAb.{u, r, w} Λ))
        (ComplexShape.up ℕ)).inv.app _) ≫ _
  rw [reassoc_of% h₁, h₂, Category.assoc]

variable
  [EnoughInjectives (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w})]

/-- **The pro-étale cohomology of the sheaf attached to a representation is its continuous
cohomology, naturally** in morphisms of representations with good coefficients. -/
lemma rightDerivedRepAbSheafIso_hom_naturality {X Y : TopRep.{max u w} Λ (galoisGroup K)}
    (hX : GoodCoefficients X) (hY : GoodCoefficients Y) (g : X ⟶ Y) (n : ℕ) :
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived n).map
        ((repAbSheaf.{u, r, max u w} Λ).map g) ≫ (rightDerivedRepAbSheafIso Y hY n).hom =
      (rightDerivedRepAbSheafIso X hX n).hom ≫
        (underlyingAb.{u, r, w} Λ).map (HomologicalComplex.homologyMap
          (((TopRep.invariantsFunctor Λ (galoisGroup K)).mapHomologicalComplex _).map
            (TopRep.resolution'Map g)) n) := by
  have := quasiIso_sheafResolutionι hX
  have := quasiIso_sheafResolutionι hY
  have hacyc : ∀ (Z : TopRep.{max u w} Λ (galoisGroup K)) (hZ : GoodCoefficients Z) (q : ℕ),
      Stacks.RightDerivedComp.acyclic
        (Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w})
        ((sheafResolution Λ Z).X q) := fun Z hZ q m hm ↦ by
    have := (hZ.resolutionX q).nonarchimedean
    have := (hZ.resolutionX q).t2Space
    exact isZero_rightDerived_coindAbSheaf (TopRep.resolutionX Z q)
      (hZ.resolutionX q).continuous_action (hZ.resolutionX q).isProDiscrete m hm
  have comm : sheafResolutionι Λ X ≫
      ((repAbSheaf.{u, r, max u w} Λ).mapHomologicalComplex _).map (TopRep.resolution'Map g) =
        (CochainComplex.single₀ _).map ((repAbSheaf Λ).map g) ≫ sheafResolutionι Λ Y := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    simp only [CochainComplex.fromSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
      CochainComplex.single₀_map_f_zero, sheafResolutionι,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, Functor.mapHomologicalComplex_map_f,
      TopRep.resolution'Map_f]
    exact (((repAbSheaf.{u, r, max u w} Λ).map_comp _ _).symm.trans
      (congrArg (repAbSheaf Λ).map (TopRep.resolutionXMap_comp_d g 0).symm)).trans
      ((repAbSheaf Λ).map_comp _ _)
  have nat := Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_hom_naturality
    (Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w})
    (sheafResolutionι Λ X) (sheafResolutionι Λ Y) (hacyc X hX) (hacyc Y hY)
    ((repAbSheaf Λ).map g) _ comm n
  have e₁ : ((Sheaf.Γ (Scheme.ProEt.topology (base K))
      AddCommGrpCat.{max (u + 1) r w}).rightDerived n).map ((repAbSheaf.{u, r, max u w} Λ).map g) ≫
        (Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ (sheafResolutionι Λ Y)
          (hacyc Y hY) n).hom =
      (Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ (sheafResolutionι Λ X)
          (hacyc X hX) n).hom ≫ HomologicalComplex.homologyMap
        (((Sheaf.Γ (Scheme.ProEt.topology (base K))
          AddCommGrpCat.{max (u + 1) r w}).mapHomologicalComplex _).map
            (((repAbSheaf.{u, r, max u w} Λ).mapHomologicalComplex _).map
              (TopRep.resolution'Map g))) n := nat
  have e₂ := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (mapSheafResolutionIso_hom_naturality (K := K) g)
  simp only [HomologicalComplex.homologyMap_comp] at e₂
  have e₃ := underlyingAbHomologyIso_hom_naturality.{u, r, w} (((TopRep.invariantsFunctor Λ
    (galoisGroup K)).mapHomologicalComplex _).map (TopRep.resolution'Map g)) n
  change _ ≫ (Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ (sheafResolutionι Λ Y)
        (hacyc Y hY) n).hom ≫ HomologicalComplex.homologyMap (mapSheafResolutionIso Y).hom n ≫
        (underlyingAbHomologyIso.{u, r, w} Λ (TopRep.homogeneousCochains Y) n).hom =
    ((Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ (sheafResolutionι Λ X)
        (hacyc X hX) n).hom ≫ HomologicalComplex.homologyMap (mapSheafResolutionIso X).hom n ≫
        (underlyingAbHomologyIso.{u, r, w} Λ (TopRep.homogeneousCochains X) n).hom) ≫ _
  exact ((reassoc_of% e₁) _).trans ((_ ≫= (reassoc_of% e₂) _).trans ((_ ≫= _ ≫= e₃).trans
    ((_ ≫= (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)))

end Naturality

/-! ### Scalars -/

section Linear

variable {Λ : Type r} [CommRing Λ] [TopologicalSpace Λ]

/-- The functor `repSheaf`, from topological representations to sheaves of continuous equivariant
functions, is `Λ`-linear: it carries `c • f` to `c • repSheaf.map f`. -/
instance linear_repSheaf : (repSheaf.{u, r, w} (K := K) Λ).Linear Λ where
  map_smul _ _ := by
    ext V z
    rfl

/-- Multiplication by a scalar on a representation induces multiplication by that scalar on its
continuous cohomology. -/
lemma homologyMap_resolution'Map_smul_id (X : TopRep.{max u w} Λ (galoisGroup K)) (c : Λ)
    (n : ℕ) :
    HomologicalComplex.homologyMap
      (((TopRep.invariantsFunctor Λ (galoisGroup K)).mapHomologicalComplex _).map
        (TopRep.resolution'Map (c • 𝟙 X))) n = c • 𝟙 (continuousCohomology n X) := by
  rw [TopRep.resolution'Map_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  change ShortComplex.homologyMap (c • 𝟙 ((TopRep.homogeneousCochains X).sc n)) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

end Linear

/-! ### Case (2) of Stacks 09B4, as `Λ`-modules -/

section Adic

variable (K) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) (M : Type w)
  [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]

/-- **Stacks Project, Tag 09B4, case (2), as `Λ`-modules.** In the situation of
`rightDerivedAdicSheafIso`, the identification `Hⁱ(Spec(K)_proét, M^∧) ≅ Hⁱ_cont(G, M)` is
`Λ`-linear: for every `c ∈ Λ` it carries the endomorphism of `Hⁱ(Spec(K)_proét, M^∧)` induced by
multiplication by `c` on the sheaf of `Λ`-modules `M^∧` to multiplication by `c` on the
`Λ`-module `Hⁱ_cont(G, M)`. -/
theorem rightDerivedAdicSheafIso_hom_smul
    (ρ : Representation Λ (galoisGroup K) M)
    (hρ : letI := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) (i : ℕ) (c : Λ) :
    letI : TopologicalSpace Λ := I.adicTopology
    letI := I.adicModuleTopology M
    letI := hasSheafify_galois.{u, r, w} K
    letI := enoughInjectives_galois.{u, r, w} K
    letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
      (Scheme.ProEt.topology (base K))
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived i).map
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat)).map
          (c • 𝟙 (adicSheaf Λ K I M ρ hρ))) ≫ (rightDerivedAdicSheafIso K Λ I M ρ hρ i).hom =
      (rightDerivedAdicSheafIso K Λ I M ρ hρ i).hom ≫
        (underlyingAb.{u, r, w} Λ).map (c • 𝟙 (continuousCohomology i (uliftRep.{u} ρ hρ))) := by
  let : TopologicalSpace Λ := I.adicTopology
  let := I.adicModuleTopology M
  let := hasSheafify_galois.{u, r, w} K
  let := enoughInjectives_galois.{u, r, w} K
  let := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
    (Scheme.ProEt.topology (base K))
  let R := (Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived i
  let F := sheafCompose (Scheme.ProEt.topology (base K))
    (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat)
  let e := completionIsoContSheaf ρ (adicDiagram Λ I ρ) (adic_hopen K Λ I M ρ)
    (adic_hbasis K Λ I M ρ) (adic_hsep K Λ I M ρ) (adic_hcomp K Λ I M ρ) ≪≫
      contSheafIsoRepSheaf ρ hρ
  have hgood := goodCoefficients_uliftRep ρ hρ (adicDiagram Λ I ρ) (adic_hopen K Λ I M ρ)
    (adic_hbasis K Λ I M ρ) (adic_hsep K Λ I M ρ) (adic_hcomp K Λ I M ρ)
  have hdef : (rightDerivedAdicSheafIso K Λ I M ρ hρ i).hom =
      R.map (F.map e.hom) ≫ (rightDerivedRepAbSheafIso (uliftRep.{u} ρ hρ) hgood i).hom := rfl
  have he : R.map (F.map (c • 𝟙 _)) ≫ R.map (F.map e.hom) =
      R.map (F.map e.hom) ≫
        R.map ((repAbSheaf.{u, r, max u w} Λ).map (c • 𝟙 (uliftRep.{u} ρ hρ))) := by
    rw [← R.map_comp, ← R.map_comp, ← F.map_comp, Functor.comp_map, ← F.map_comp,
      Linear.smul_comp, Category.id_comp, (repSheaf.{u, r, max u w} Λ).map_smul,
      CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id]
  have hnat := rightDerivedRepAbSheafIso_hom_naturality hgood hgood (c • 𝟙 (uliftRep.{u} ρ hρ)) i
  rw [homologyMap_resolution'Map_smul_id] at hnat
  rw [hdef]
  exact ((reassoc_of% he) _).trans ((_ ≫= hnat).trans (Category.assoc _ _ _).symm)

/-- The `Λ`-module `Hⁱ(Spec(K)_proét, M^∧)`: the abelian group `Rⁱ Γ(M^∧)` of the underlying
abelian sheaf, on which `c ∈ Λ` acts by the image under `Rⁱ Γ` of multiplication by `c` on the
sheaf of `Λ`-modules `M^∧`. -/
def rightDerivedAdicSheafModule
    (ρ : Representation Λ (galoisGroup K) M)
    (hρ : letI := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) (i : ℕ) :
    ModuleCat.{max (u + 1) r w} Λ :=
  letI := hasSheafify_galois.{u, r, w} K
  letI := enoughInjectives_galois.{u, r, w} K
  letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
    (Scheme.ProEt.topology (base K))
  haveI := Stacks.DerivedLinear.rightDerived_additive
    (Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}) i
  ModuleCat.mkOfSMul ((Stacks.ModuleCatLift.mapEndRingHom
    (sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat) ⋙
      (Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived i)
    (adicSheaf Λ K I M ρ hρ)).comp (algebraMap Λ (End (adicSheaf Λ K I M ρ hρ))))

/-- **Stacks Project, Tag 09B4, case (2), as `Λ`-modules.** In the situation of
`rightDerivedAdicSheafIso`, the pro-étale cohomology `Hⁱ(Spec(K)_proét, M^∧)`, a `Λ`-module
through the action of `Λ` on `M^∧`, is isomorphic as a `Λ`-module to the continuous cohomology
`Hⁱ_cont(G, M)`, by the identification `rightDerivedAdicSheafIso`. -/
@[stacks 09B4 "case (2), as Λ-modules"]
def rightDerivedAdicSheafLinearEquiv
    (ρ : Representation Λ (galoisGroup K) M)
    (hρ : letI := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) (i : ℕ) :
    letI : TopologicalSpace Λ := I.adicTopology
    letI := I.adicModuleTopology M
    rightDerivedAdicSheafModule K Λ I M ρ hρ i ≃ₗ[Λ]
      ULift.{max (u + 1) r} (continuousCohomology i (uliftRep.{u} ρ hρ)) :=
  letI : TopologicalSpace Λ := I.adicTopology
  letI := I.adicModuleTopology M
  AddEquiv.toLinearEquiv (rightDerivedAdicSheafIso K Λ I M ρ hρ i).addCommGroupIsoToAddEquiv
    fun c x ↦ congr($(rightDerivedAdicSheafIso_hom_smul K Λ I M ρ hρ i c).hom x)

/-- The `Λ`-linear identification is the comparison of abelian groups. -/
lemma rightDerivedAdicSheafLinearEquiv_apply
    (ρ : Representation Λ (galoisGroup K) M)
    (hρ : letI := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) (i : ℕ)
    (x : rightDerivedAdicSheafModule K Λ I M ρ hρ i) :
    letI : TopologicalSpace Λ := I.adicTopology
    letI := I.adicModuleTopology M
    rightDerivedAdicSheafLinearEquiv K Λ I M ρ hρ i x =
      (rightDerivedAdicSheafIso K Λ I M ρ hρ i).hom x :=
  rfl

end Adic

end AlgebraicGeometry.GaloisSheaf
