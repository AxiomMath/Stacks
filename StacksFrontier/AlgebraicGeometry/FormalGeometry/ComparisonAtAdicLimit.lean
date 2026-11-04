module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsAdicLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NearVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TildeAdicQuotientTower
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cover
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Naturality

/-!
# The comparison at a neighbourhood is onto, from realization on that neighbourhood

Let `A` be a commutative ring, `I ⊆ 𝔞` ideals, `U = Spec(A) ∖ V(𝔞)`, `ℱ` a module on `U` and
`V ⊆ U` a neighbourhood of the formal locus `U ∩ V(I)`. The comparison

`Stacks.Algebraization.comparisonAt : Γ(V, ℱ) ⟶ lim_n Γ(U, ℱ/Iⁿℱ)`

reduces a section modulo `Iⁿ` on `V` and then extends it from `V` to all of `U`, the extension
being an isomorphism because the quotients vanish off the formal locus. Inverting that
isomorphism, the comparison is onto exactly when every compatible family of sections of the
quotients **on `V`** is the reduction of a single section of `ℱ` on `V`; the first section of this
file records that.

The rest of the file discharges that condition for `ℱ = M̃|_U` over a Noetherian local ring, with
`𝔞 = 𝔪` and `V` the neighbourhood cut out by an ideal `J` with `V(J) ∩ V(I) = {𝔪}`. The
sections of `ℱ/Iⁿℱ` on `V` are the sections of `(M/IⁿM)~` on `Spec(A) ∖ V(J)`, by the tower
identification `Stacks.Algebraization.quotientSystemNearVanishingTowerIso` and the identification
`Stacks.Algebraization.OpensNearVanishing.ι_image_openSet_ofZeroLocusInter` of the image of `V` in
`Spec(A)` with `Spec(A) ∖ V(J)`, so the condition is exactly the surjectivity of
`Stacks.Algebraization.complementSectionsToLimit`.

## Main results

* `Stacks.Algebraization.surjective_comparisonAt_of_realizable` — the reduction described above.
* `Stacks.Algebraization.surjective_comparisonAt_ofZeroLocusInter` — the comparison at the
  neighbourhood cut out by `J` is onto, granted the surjectivity of the canonical map
  `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)`.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a)

/-! ### The comparison at one neighbourhood, and realization there -/

/-- The inverse system `n ↦ Γ(V, ℱ/Iⁿℱ)` of sections of the ideal-power quotients on a single
neighbourhood `V` of the formal locus. Restriction from `U` to `V` identifies it with
`Stacks.Algebraization.formalSections`, by
`Stacks.Algebraization.isIso_quotientSystemNearVanishing_res`. -/
public def quotientSectionsAt : ℕᵒᵖ ⥤ Ab.{u} :=
  quotientSystemNearVanishing A I a F ⋙ Scheme.Modules.toPresheaf _ ⋙
    (CategoryTheory.evaluation _ Ab.{u}).obj (op V.openSet)

/-- The `n`-th term of `quotientSectionsAt` is the group of sections of `ℱ/Iⁿℱ` on `V`. -/
public theorem quotientSectionsAt_obj (n : ℕᵒᵖ) :
    (quotientSectionsAt A I a F V).obj n =
      Γ((quotientSystemNearVanishing A I a F).obj n, V.openSet) :=
  rfl

/-- The transition maps of `quotientSectionsAt` are those of the quotient tower, evaluated on
`V`. -/
public theorem quotientSectionsAt_map {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (quotientSectionsAt A I a F V).map g =
      ((quotientSystemNearVanishing A I a F).map g).app V.openSet :=
  rfl

/-- Two factorizations of a morphism of abelian groups through different intermediate objects
agree pointwise. -/
private theorem apply_comp_eq_apply_comp {X Y Y' Z : Ab.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (x : ToType X) :
    ConcreteCategory.hom g (ConcreteCategory.hom f x) =
      ConcreteCategory.hom g' (ConcreteCategory.hom f' x) := by
  rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]

/-- **The comparison at a neighbourhood is onto as soon as every compatible family of sections of
the quotients on that neighbourhood is a reduction.** Restriction from `U` to `V` is an
isomorphism on the quotients, so a compatible family of sections on `U` is the same thing as a
compatible family on `V`; the comparison sends a section of `ℱ` on `V` to the family of its
reductions. -/
public theorem surjective_comparisonAt_of_realizable
    (hreal : ∀ s : ((quotientSectionsAt A I a F V) ⋙ forget Ab.{u}).sections,
      ∃ t : ToType ((sectionsNearVanishing A I a F).obj V),
        ∀ n : ℕᵒᵖ, ConcreteCategory.hom (projNearVanishing A I a F V n) t = s.val n) :
    Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V)) := by
  intro z
  have hcompat : ∀ {m n : ℕᵒᵖ} (g : m ⟶ n),
      ConcreteCategory.hom ((quotientSectionsAt A I a F V).map g)
          (ConcreteCategory.hom (resNearVanishing A I a F V m)
            (ConcreteCategory.hom (limit.π (formalSections A I a F) m) z)) =
        ConcreteCategory.hom (resNearVanishing A I a F V n)
          (ConcreteCategory.hom (limit.π (formalSections A I a F) n) z) := by
    intro m n g
    refine (apply_comp_eq_apply_comp
      (formalSections_map_comp_resNearVanishing A I a F V g).symm _).trans ?_
    rw [← ConcreteCategory.comp_apply (limit.π _ m), limit.w]
  obtain ⟨t, ht⟩ := hreal
    ⟨fun n => ConcreteCategory.hom (resNearVanishing A I a F V n)
        (ConcreteCategory.hom (limit.π (formalSections A I a F) n) z),
      fun {_ _} g => hcompat g⟩
  refine ⟨t, Concrete.limit_ext (formalSections A I a F) _ _ fun n => ?_⟩
  have hπ : ConcreteCategory.hom (limit.π (formalSections A I a F) n)
        (ConcreteCategory.hom (comparisonAt A I a F V) t) =
      ConcreteCategory.hom (inv (resNearVanishing A I a F V n))
        (ConcreteCategory.hom (projNearVanishing A I a F V n) t) :=
    (ConcreteCategory.comp_apply (comparisonAt A I a F V)
          (limit.π (formalSections A I a F) n) t).symm.trans
      ((congrArg (fun φ : (sectionsNearVanishing A I a F).obj V ⟶
            (formalSections A I a F).obj n => ConcreteCategory.hom φ t)
          (comparisonAt_π A I a F V n)).trans
        (ConcreteCategory.comp_apply (projNearVanishing A I a F V n)
          (inv (resNearVanishing A I a F V n)) t))
  rw [hπ, ht n]
  exact ((ConcreteCategory.comp_apply (resNearVanishing A I a F V n)
        (inv (resNearVanishing A I a F V n)) _).symm.trans
    (congrArg (fun φ : (formalSections A I a F).obj n ⟶ (formalSections A I a F).obj n =>
        ConcreteCategory.hom φ (ConcreteCategory.hom (limit.π (formalSections A I a F) n) z))
      (IsIso.hom_inv_id (resNearVanishing A I a F V n))))

/-! ### Two identifications of sections, both definitional -/

variable {A I a}

/-- The tower of sections, on an open `W` of `Spec(A) ∖ V(𝔟)`, of the sheaves associated to a
tower `T` of `A`-modules. -/
public def towerSectionsOn (b : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (W : (complementZeroLocus A b : Scheme).Opens) : ℕᵒᵖ ⥤ Ab.{u} :=
  (T ⋙ tilde.functor (CommRingCat.of A)) ⋙
    Scheme.Modules.restrictFunctor (complementZeroLocus A b).ι ⋙
      Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj (op W)

/-- The terms of `Stacks.Algebraization.towerSectionsOn` are the locally fractional sections on
the image of `W` in `Spec(A)`. -/
public theorem towerSectionsOn_obj (b : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (W : (complementZeroLocus A b : Scheme).Opens) (n : ℕᵒᵖ) :
    (towerSectionsOn b T W).obj n =
      AddCommGrpCat.of (moduleSections (T.obj n) ((complementZeroLocus A b).ι ''ᵁ W)) :=
  rfl

/-- The transition maps of `Stacks.Algebraization.towerSectionsOn` act on numerators. The tower
is left opaque, so no sheaf construction attached to a specific tower is unfolded. -/
public theorem towerSectionsOn_forget_map_apply (b : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (W : (complementZeroLocus A b : Scheme).Opens) {m n : ℕᵒᵖ} (g : m ⟶ n)
    (x : moduleSections (T.obj m) ((complementZeroLocus A b).ι ''ᵁ W)) :
    (towerSectionsOn b T W ⋙ forget Ab.{u}).map g x =
      moduleSectionsMap (T.map g) ((complementZeroLocus A b).ι ''ᵁ W) x :=
  rfl

/-- A module map acts on the sections of the restricted associated sheaves by acting on the
numerators. -/
public theorem restrictFunctor_tilde_map_app_apply (b : Ideal A)
    (W : (complementZeroLocus A b : Scheme).Opens) {N₁ N₂ : ModuleCat.{u} A} (φ : N₁ ⟶ N₂)
    (x : moduleSections N₁ ((complementZeroLocus A b).ι ''ᵁ W)) :
    ConcreteCategory.hom
        (((Scheme.Modules.restrictFunctor (complementZeroLocus A b).ι).map
          ((tilde.functor (CommRingCat.of A)).map φ)).app W) x =
      moduleSectionsMap φ ((complementZeroLocus A b).ι ''ᵁ W) x :=
  rfl

/-- Equal morphisms of modules on a scheme act equally on sections. Stated with the scheme and
the two modules opaque, so that no sheaf construction is unfolded. -/
public theorem congr_app_apply {X : Scheme.{u}} {N₁ N₂ : X.Modules} {φ ψ : N₁ ⟶ N₂} (h : φ = ψ)
    (W : X.Opens) (x : ToType Γ(N₁, W)) :
    ConcreteCategory.hom (φ.app W) x = ConcreteCategory.hom (ψ.app W) x :=
  congrArg (fun α : N₁ ⟶ N₂ => ConcreteCategory.hom (α.app W) x) h

/-- A composite of morphisms of modules acts on sections as the composite of the actions. -/
private theorem comp_app_apply {X : Scheme.{u}} {N₁ N₂ N₃ : X.Modules} (φ : N₁ ⟶ N₂) (ψ : N₂ ⟶ N₃)
    (W : X.Opens) (x : ToType Γ(N₁, W)) :
    ConcreteCategory.hom ((φ ≫ ψ).app W) x =
      ConcreteCategory.hom (ψ.app W) (ConcreteCategory.hom (φ.app W) x) :=
  rfl

/-- Transport of sections along an equality of opens commutes with the action of a module map:
both are restriction maps, and a module map acts pointwise. -/
public theorem moduleSectionsCongr_moduleSectionsMap {N₁ N₂ : ModuleCat.{u} A} (φ : N₁ ⟶ N₂)
    {U₁ U₂ : Opens (PrimeSpectrum.Top A)} (h : U₁ = U₂) (x : moduleSections N₁ U₁) :
    moduleSectionsCongr N₂ h (moduleSectionsMap φ U₁ x) =
      moduleSectionsMap φ U₂ (moduleSectionsCongr N₁ h x) :=
  rfl

/-- **The transition maps of the tower `n ↦ M/IⁿM` are Mathlib's
`AdicCompletion.transitionMap`**, in the spelling of
`Stacks.LocalCohomology.idealPowerQuotientTower`: both send the class of `x` to the class of `x`.
The same statement in the spelling of
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` is
`Dualizing.adicQuotientModuleSystem_map`; that common canonical form is what lets the two towers
be compared without unfolding either. -/
public theorem idealPowerQuotientTower_map (I : Ideal A) (N : ModuleCat.{u} A) {m n : ℕ}
    (h : m ≤ n) :
    (idealPowerQuotientTower I N).map (homOfLE h).op =
      ModuleCat.ofHom (AdicCompletion.transitionMap I N h) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using Submodule.Quotient.induction_on with
  | _ y => rfl

/-- A compatible family transported along a map of towers of abelian groups. -/
public def transportSections {F G : ℕᵒᵖ ⥤ Ab.{u}} (α : F ⟶ G)
    (s : (F ⋙ forget Ab.{u}).sections) : (G ⋙ forget Ab.{u}).sections :=
  ⟨fun n => ConcreteCategory.hom (α.app n) (s.val n), fun {m n} g =>
    ((ConcreteCategory.comp_apply (α.app m) (G.map g) (s.val m)).symm.trans
      ((congrArg (fun φ : F.obj m ⟶ G.obj n => ConcreteCategory.hom φ (s.val m))
          (α.naturality g).symm).trans
        (ConcreteCategory.comp_apply (F.map g) (α.app n) (s.val m)))).trans
      (congrArg (ConcreteCategory.hom (α.app n)) (s.property g))⟩

/-- The `n`-th entry of a transported family is the image of the `n`-th entry under `α`. -/
public theorem transportSections_val {F G : ℕᵒᵖ ⥤ Ab.{u}} (α : F ⟶ G)
    (s : (F ⋙ forget Ab.{u}).sections) (n : ℕᵒᵖ) :
    (transportSections α s).val n = ConcreteCategory.hom (α.app n) (s.val n) :=
  rfl

/-! ### Realization at the neighbourhood cut out by an ideal -/

variable (A)

variable [IsLocalRing A] [IsNoetherianRing A] (I J : Ideal A)
  (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
    {closedPoint A})
  (M : ModuleCat.{u} A)
  (Fm : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)
  (e : Fm ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
    (complementZeroLocus A (maximalIdeal A)).ι)

include hV in
/-- **Realization of a compatible family of locally fractional sections.** Let `W` be an open of
`Spec(A)` which is the affine complement `Spec(A) ∖ V(J)`. Then every compatible family of
sections of the `(M/IⁿM)~` on `W` is the family of reductions of a single section of `M̃` on `W`,
granted the surjectivity of the canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)`.

This is `Stacks.Algebraization.surjective_complementSectionsToLimit` transported along the
equality of opens; nothing about the module `ℱ` or about neighbourhoods of the formal locus
enters, and the transition maps of the tower are written in the canonical form
`AdicCompletion.transitionMap`. -/
public theorem realizable_of_moduleSections (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) [Module.Finite A M] [IsAdicComplete I M]
    (hcD : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1)))
    (W : Opens (PrimeSpectrum.Top A))
    (hW : W = (complementZeroLocus A J).ι ''ᵁ ⊤)
    (σ : ∀ nn : ℕ, moduleSections (ModuleCat.of A (M ⧸ (I ^ nn • (⊤ : Submodule A M)))) W)
    (hσ : ∀ {k l : ℕ} (h : k ≤ l),
      moduleSectionsMap (ModuleCat.ofHom (AdicCompletion.transitionMap I M h)) W (σ l) = σ k) :
    ∃ x : moduleSections M W, ∀ nn : ℕ,
      moduleSectionsMap (ModuleCat.ofHom
        (Submodule.mkQ (I ^ nn • (⊤ : Submodule A M)))) W x = σ nn := by
  have hcompat : ∀ {m n : ℕᵒᵖ} (g : m ⟶ n),
      ConcreteCategory.hom ((complementSectionsAdicTower A I J M).map g)
          (moduleSectionsCongr (ModuleCat.of A
            (M ⧸ (I ^ m.unop • (⊤ : Submodule A M)))) hW (σ m.unop)) =
        moduleSectionsCongr (ModuleCat.of A
          (M ⧸ (I ^ n.unop • (⊤ : Submodule A M)))) hW (σ n.unop) := by
    intro m n g
    refine Eq.trans (congrArg (fun φ : m ⟶ n => ConcreteCategory.hom
        ((complementSectionsAdicTower A I J M).map φ)
        (moduleSectionsCongr (ModuleCat.of A
          (M ⧸ (I ^ m.unop • (⊤ : Submodule A M)))) hW (σ m.unop)))
      (Subsingleton.elim g (homOfLE (leOfHom g.unop)).op)) ?_
    refine Eq.trans (congrArg
      (fun φ : (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj m ⟶
          (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj n =>
        ConcreteCategory.hom ((affineComplementSectionsFunctor A J).map φ)
          (moduleSectionsCongr (ModuleCat.of A
            (M ⧸ (I ^ m.unop • (⊤ : Submodule A M)))) hW (σ m.unop)))
      (Dualizing.adicQuotientModuleSystem_map A I M (leOfHom g.unop))) ?_
    refine Eq.trans (moduleSectionsCongr_moduleSectionsMap
      (ModuleCat.ofHom (AdicCompletion.transitionMap I M (leOfHom g.unop))) hW (σ m.unop)).symm ?_
    exact congrArg (moduleSectionsCongr (ModuleCat.of A
      (M ⧸ (I ^ n.unop • (⊤ : Submodule A M)))) hW) (hσ (leOfHom g.unop))
  obtain ⟨z, hz⟩ := ModuleCat.exists_limit_π_eq_of_sections (complementSectionsAdicTower A I J M)
    ⟨fun n => moduleSectionsCongr (ModuleCat.of A
        (M ⧸ (I ^ n.unop • (⊤ : Submodule A M)))) hW (σ n.unop),
      fun {_ _} g => hcompat g⟩
  obtain ⟨t, ht⟩ := surjective_complementSectionsToLimit A I J hJ D M hV hcD z
  refine ⟨(moduleSectionsCongr M hW).symm t, fun nn => ?_⟩
  refine (moduleSectionsCongr (ModuleCat.of A
    (M ⧸ (I ^ nn • (⊤ : Submodule A M)))) hW).injective ?_
  refine ((moduleSectionsCongr_moduleSectionsMap
        (ModuleCat.ofHom (Submodule.mkQ (I ^ nn • (⊤ : Submodule A M)))) hW
          ((moduleSectionsCongr M hW).symm t)).trans
      ((congrArg (moduleSectionsMap (ModuleCat.ofHom
            (Submodule.mkQ (I ^ nn • (⊤ : Submodule A M))))
            ((complementZeroLocus A J).ι ''ᵁ ⊤))
          ((moduleSectionsCongr M hW).apply_symm_apply t)).trans ?_)).trans (hz (op nn))
  exact ((congrArg (fun φ : (affineComplementSectionsFunctor A J).obj M ⟶
          (complementSectionsAdicTower A I J M).obj (op nn) => ConcreteCategory.hom φ t)
        (complementSectionsToLimit_π A I J M nn)).symm).trans
    (congrArg (ConcreteCategory.hom
      (limit.π (complementSectionsAdicTower A I J M) (op nn))) ht)

omit [IsNoetherianRing A] in
/-- The image of the neighbourhood cut out by `J` in `Spec(A)` is the affine complement
`Spec(A) ∖ V(J)`, written as the image of the whole of that open subscheme. -/
public theorem ι_image_openSet_ofZeroLocusInter_eq_ι_image_top :
    (complementZeroLocus A (maximalIdeal A)).ι ''ᵁ
        (OpensNearVanishing.ofZeroLocusInter I J hV).openSet =
      (complementZeroLocus A J).ι ''ᵁ ⊤ :=
  (OpensNearVanishing.ι_image_openSet_ofZeroLocusInter I J hV).trans
    (Scheme.Opens.ι_image_top (complementZeroLocus A J)).symm

include e in
/-- **The tower of sections of `ℱ/Iⁿℱ` on the neighbourhood cut out by `J` is the tower of
sections of the `(M/IⁿM)~` on the image of that neighbourhood in `Spec(A)`.** -/
public def quotientSectionsAtTowerIso :
    quotientSectionsAt A I (maximalIdeal A) Fm (OpensNearVanishing.ofZeroLocusInter I J hV) ≅
      towerSectionsOn (maximalIdeal A) (idealPowerQuotientTower I M)
        (OpensNearVanishing.ofZeroLocusInter I J hV).openSet :=
  Functor.isoWhiskerRight (quotientSystemNearVanishingTowerIso A I (maximalIdeal A) Fm M e)
    (Scheme.Modules.toPresheaf _ ⋙
      (CategoryTheory.evaluation _ Ab.{u}).obj
        (op (OpensNearVanishing.ofZeroLocusInter I J hV).openSet))

include e in
/-- **Realization on the neighbourhood cut out by `J`.** Every compatible family of sections of
`ℱ/Iⁿℱ` on that neighbourhood is the family of reductions of a single section of `ℱ` there,
granted the surjectivity of the canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)`.

The family is carried over to a compatible family of sections of the `(M/IⁿM)~` on
`Spec(A) ∖ V(J)` by the tower identification, where
`Stacks.Algebraization.realizable_of_moduleSections` realizes it; the realizing section is
carried back along the identification of `ℱ` with `M̃|_U`. -/
public theorem realizable_ofZeroLocusInter (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) [Module.Finite A M] [IsAdicComplete I M]
    (hcD : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1)))
    (s : ((quotientSectionsAt A I (maximalIdeal A) Fm
      (OpensNearVanishing.ofZeroLocusInter I J hV)) ⋙ forget Ab.{u}).sections) :
    ∃ t : ToType ((sectionsNearVanishing A I (maximalIdeal A) Fm).obj
        (OpensNearVanishing.ofZeroLocusInter I J hV)),
      ∀ n : ℕᵒᵖ, ConcreteCategory.hom
        (projNearVanishing A I (maximalIdeal A) Fm
          (OpensNearVanishing.ofZeroLocusInter I J hV) n) t = s.val n := by
  have hW := ι_image_openSet_ofZeroLocusInter_eq_ι_image_top A I J hV
  have hσ : ∀ {k l : ℕ} (h : k ≤ l),
      moduleSectionsMap (ModuleCat.ofHom (AdicCompletion.transitionMap I M h))
          ((complementZeroLocus A (maximalIdeal A)).ι ''ᵁ
            (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)
          ((transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).val (op l)) =
        (transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).val (op k) := by
    intro k l h
    refine Eq.trans (congrArg (fun φ : (idealPowerQuotientTower I M).obj (op l) ⟶
        (idealPowerQuotientTower I M).obj (op k) =>
        moduleSectionsMap φ ((complementZeroLocus A (maximalIdeal A)).ι ''ᵁ
            (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)
          ((transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).val (op l)))
      (idealPowerQuotientTower_map I M h).symm) ?_
    exact (towerSectionsOn_forget_map_apply (maximalIdeal A) (idealPowerQuotientTower I M)
      (OpensNearVanishing.ofZeroLocusInter I J hV).openSet (homOfLE h).op
      ((transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).val
        (op l))).symm.trans
      ((transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).property
        (homOfLE h).op)
  obtain ⟨x, hx⟩ := realizable_of_moduleSections A I J hV M hJ D hcD
    ((complementZeroLocus A (maximalIdeal A)).ι ''ᵁ
      (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) hW
    (fun nn => (transportSections (quotientSectionsAtTowerIso A I J hV M Fm e).hom s).val (op nn))
    (fun {_ _} h => hσ h)
  refine ⟨ConcreteCategory.hom (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) x,
    fun n => ?_⟩
  obtain ⟨n⟩ := n
  refine (ConcreteCategory.bijective_of_isIso
    ((quotientSectionsAtTowerIso A I J hV M Fm e).hom.app (op n))).1 ?_
  have he : ConcreteCategory.hom (e.hom.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)
        (ConcreteCategory.hom
          (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) x) = x :=
    (comp_app_apply e.inv e.hom (OpensNearVanishing.ofZeroLocusInter I J hV).openSet _).symm.trans
      (congr_app_apply e.inv_hom_id (OpensNearVanishing.ofZeroLocusInter I J hV).openSet x)
  have hL : ConcreteCategory.hom ((quotientSectionsAtTowerIso A I J hV M Fm e).hom.app (op n))
        (ConcreteCategory.hom (projNearVanishing A I (maximalIdeal A) Fm
            (OpensNearVanishing.ofZeroLocusInter I J hV) (op n))
          (ConcreteCategory.hom
            (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) x)) =
      moduleSectionsMap (Dualizing.adicQuotientProjection A I M n)
        ((complementZeroLocus A (maximalIdeal A)).ι ''ᵁ
          (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) x := by
    refine Eq.trans
      (comp_app_apply _ _ (OpensNearVanishing.ofZeroLocusInter I J hV).openSet _).symm (Eq.trans
        (congr_app_apply
          (π_comp_quotientSystemNearVanishingTowerIso_hom_app A I (maximalIdeal A) Fm M e n)
          (OpensNearVanishing.ofZeroLocusInter I J hV).openSet _) ?_)
    rw [comp_app_apply, he]
    exact restrictFunctor_tilde_map_app_apply (maximalIdeal A)
      (OpensNearVanishing.ofZeroLocusInter I J hV).openSet
      (Dualizing.adicQuotientProjection A I M n) x
  exact hL.trans ((hx n).trans
    (transportSections_val (quotientSectionsAtTowerIso A I J hV M Fm e).hom s (op n)))

include e in
/-- **The comparison at the neighbourhood cut out by `J` is onto**, granted the surjectivity of
the canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)`. This is the comparison clause of Stacks 0DXQ at
`i = 0`, in the form the conclusion of Stacks 0DXR consumes. -/
public theorem surjective_comparisonAt_ofZeroLocusInter (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) [Module.Finite A M] [IsAdicComplete I M]
    (hcD : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1))) :
    Function.Surjective (ConcreteCategory.hom
      (comparisonAt A I (maximalIdeal A) Fm (OpensNearVanishing.ofZeroLocusInter I J hV))) :=
  surjective_comparisonAt_of_realizable A I (maximalIdeal A) Fm
    (OpensNearVanishing.ofZeroLocusInter I J hV)
    (realizable_ofZeroLocusInter A I J hV M Fm e hJ D hcD)

end Stacks.Algebraization

end
