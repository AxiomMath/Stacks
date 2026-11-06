module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechGlobalClass
public import StacksFrontier.AlgebraicGeometry.DeRham.AffineDeRhamCohomologyCech
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsGeneratorCalculus
public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechBaseCochain

/-!
# The pull-back of de Rham cohomology on Čech classes of global forms

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. A closed global form `σ` of `Y/S` has a
Čech class for any open covering of `Y`, namely that of the cochain `t ↦ σ|_{V_t}`, and its
pull-back `f^*σ` along the canonical map of de Rham complexes ([Stacks, Tag 07HX]) has one for any
open covering of `X`. This file proves that the pull-back of de Rham cohomology of [Stacks,
Tag 0FL6], read in the module realization of de Rham cohomology (where the cup product lives),
carries the first class to the second; and, for `Y` and `S` affine, computes the restrictions of
`f^*σ` to affine opens of `X` as the ring-level pull-backs of forms.

## Main definitions

* `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamPullbackModule`: `f^* : H^k_{dR}(Y/S) ⟶ H^k_{dR}(X/S)`
  in the module realization.
* `AlgebraicGeometry.DeRhamKatzOdaCech.pullbackGlobalForm`: the pull-back of a global form.
* `AlgebraicGeometry.DeRhamKatzOdaCech.abelianCycle`: the cocycle of the de Rham complex of
  abelian sheaves given by a closed global form.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.classMap_restrictTot_abelianCycle`: the Čech class of a
  closed global form is its class in the abelian realization.
* `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamPullbackModule_classMap_restrictTot`: **`f^*` on Čech
  classes of closed global forms.**
* `AlgebraicGeometry.DeRhamKatzOdaCech.affineClassMap_cocycleClass`: the class map
  `H^b(Ω^•_{A/R}) ⟶ H^b_{dR}(Y/S)` on the class of a closed form.
* `AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv_restrict_pullbackGlobalForm`: the restriction of
  the pull-back of a global form to an affine open is the ring-level pull-back.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open Stacks.Cech.Hypercohomology (cocycleClass toMor)
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section ExtendIso

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- The inverse of the comparison of extensions, in a degree in the image of the embedding. -/
theorem _root_.HomologicalComplex.mapHomologicalComplexExtendIso_inv_f (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.mapHomologicalComplexExtendIso F K e).inv.f i' =
      F.map (K.extendXIso e h).hom ≫ (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapHomologicalComplexExtendIso F K e).hom.f i'),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h, Category.assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp, Iso.hom_inv_id]

end ExtendIso

section Generic

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The complex of global sections of the underlying complex of abelian sheaves of the
`ℤ`-indexed de Rham complex. -/
abbrev underlyingSections :=
  (sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
    ((_root_.SheafOfModules.toSheaf (structureSheafRing
      (SheafOfModules.baseRingedSpace (baseSheaf p)))).mapCochainComplexPlus.obj (deRhamPlus p))

/-- The complex of global sections of the de Rham complex of abelian sheaves. -/
abbrev abelianSections :=
  (sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
    (SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))

/-- The image of a global form in the complex of global sections of the underlying abelian
sheaves is a cocycle as soon as the form is closed. -/
theorem underlyingSections_d_globalExtend (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    ((underlyingSections p).obj.d n (n + 1)).hom (globalExtend p n s) = 0 :=
  hs

/-- The cocycle of the complex of global sections of the underlying abelian sheaves given by a
closed global form. -/
def underlyingCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    (underlyingSections p).obj.cycles n :=
  ((underlyingSections p).obj.sc n).abCyclesIso.inv
    ⟨(globalExtend p n s : ((underlyingSections p).obj.X n : Type u)), by
      refine AddMonoidHom.mem_ker.2 ?_
      have h := (underlyingSections p).obj.d_comp_XIsoOfEq_hom
        (show ((n : ℤ) + 1) = (ComplexShape.up ℤ).next n by rw [CochainComplex.next]) n
      refine (ConcreteCategory.congr_hom h.symm _).trans ?_
      refine (congrArg _ (underlyingSections_d_globalExtend p n s hs)).trans ?_
      exact (((underlyingSections p).obj.XIsoOfEq (show ((n : ℤ) + 1) =
        (ComplexShape.up ℤ).next n by rw [CochainComplex.next])).hom).hom.map_zero⟩

/-- The cocycle `underlyingCycle p n s hs` is the global form `s` in degree `n`. -/
theorem iCycles_underlyingCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    ((underlyingSections p).obj.iCycles n).hom (underlyingCycle p n s hs) = globalExtend p n s :=
  ShortComplex.abCyclesIso_inv_apply_iCycles _ _

/-- The `extendXIso` hom, evaluated on global sections, inverts `globalExtend`. -/
theorem evaluation_map_extendXIso_hom_globalExtend (n : ℕ)
    (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    ((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p))
      (op ⊤)).map
      ((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
          ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom).hom
      (globalExtend p n s) = s :=
  Iso.inv_hom_id_apply ((SheafOfModules.evaluation.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) (op ⊤)).mapIso
      ((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
          ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n))) s

/-- The differential of the complex of global sections of the `ℤ`-indexed de Rham complex, on a
global form: it is the de Rham differential of the form. -/
theorem globalSectionsComplex_d_globalExtend (n : ℕ)
    (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) =
      globalExtend p (n + 1) (((p.sectionsDeRhamComplex.d n (n + 1)).app (op ⊤)).hom s) := by
  have h := HomologicalComplex.extend_d_eq (SheafOfModules.deRhamComplex
    (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential
      (Scheme.Hom.deRhamAlgebras p))) ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = n)
    (show ComplexShape.embeddingUpNat.f (n + 1) = (n : ℤ) + 1 by simp)
  have h2 := congrArg (SheafOfModules.evaluation.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) (op ⊤)).map h
  rw [Functor.map_comp, Functor.map_comp] at h2
  refine (ConcreteCategory.congr_hom h2 (globalExtend p n s)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ (evaluation_map_extendXIso_hom_globalExtend p n s)).trans ?_
  exact (ConcreteCategory.comp_apply _ _ _).trans rfl

/-- `globalExtend` is injective. -/
theorem globalExtend_injective (n : ℕ) : Function.Injective (globalExtend p n) := by
  intro s t hst
  rw [← evaluation_map_extendXIso_hom_globalExtend p n s,
    ← evaluation_map_extendXIso_hom_globalExtend p n t, hst]

/-- A global form is closed in the complex of global sections of the `ℤ`-indexed de Rham
complex if and only if it is closed. -/
theorem globalSectionsComplex_d_globalExtend_eq_zero_iff (n : ℕ)
    (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0 ↔
      ((p.sectionsDeRhamComplex.d n (n + 1)).app (op ⊤)).hom s = 0 := by
  rw [globalSectionsComplex_d_globalExtend]
  refine ⟨fun h => globalExtend_injective p (n + 1) (h.trans (map_zero _).symm), fun h => ?_⟩
  rw [h]
  exact map_zero _

/-- The cocycle of the complex of global sections of the de Rham complex of abelian sheaves given
by a closed global form. -/
def abelianCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    (abelianSections p).obj.cycles n :=
  HomologicalComplex.cyclesMap ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
    (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).inv).hom n
    (underlyingCycle p n s hs)

/-- The comparison of the underlying and abelian de Rham complexes carries `abelianCycle p n s hs`
to `underlyingCycle p n s hs`. -/
theorem cyclesMap_abelianCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    HomologicalComplex.cyclesMap ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
      (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).hom).hom n
      (abelianCycle p n s hs) = underlyingCycle p n s hs := by
  have h := congrArg (fun φ => HomologicalComplex.cyclesMap φ.hom (n : ℤ))
    (Iso.inv_hom_id ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.mapIso
      (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))))
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    HomologicalComplex.cyclesMap_comp,
    HomologicalComplex.cyclesMap_id] at h
  exact ConcreteCategory.congr_hom h (underlyingCycle p n s hs)

/-- A global form, read as a global section of the term of degree `n` of the `ℤ`-indexed de Rham
complex of abelian sheaves. -/
def abelianExtend (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    ((abelianSections p).obj.X n : Type u) :=
  ((sectionsFunctor X.carrier ⊤).map ((SheafOfModules.deRhamAbelianComplex
    (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential
      (Scheme.Hom.deRhamAlgebras p))).extendXIso ComplexShape.embeddingUpNat rfl).inv).hom s

/-- The inverse comparison of the underlying and abelian de Rham complexes carries
`globalExtend p n s` to `abelianExtend p n s`. -/
theorem deRhamAbelianComplexPlusIso_inv_globalExtend (n : ℕ)
    (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    (((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
      (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).inv).hom.f n).hom
      (globalExtend p n s) = abelianExtend p n s := by
  have h := HomologicalComplex.mapHomologicalComplexExtendIso_inv_f
    (_root_.SheafOfModules.toSheaf.{u, u, u, u} (SheafOfModules.underlyingRingSheaf (baseSheaf p)))
    (SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)
  have h2 := congrArg (sectionsFunctor X.carrier ⊤).map h
  rw [Functor.map_comp] at h2
  show ((sectionsFunctor X.carrier ⊤).map ((HomologicalComplex.mapHomologicalComplexExtendIso
    (_root_.SheafOfModules.toSheaf.{u, u, u, u} (SheafOfModules.underlyingRingSheaf (baseSheaf p)))
    (SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))
    ComplexShape.embeddingUpNat).inv.f (ComplexShape.embeddingUpNat.f n))).hom
      (globalExtend p n s) = _
  refine (ConcreteCategory.congr_hom h2 (globalExtend p n s)).trans ?_
  have h3 : ((sectionsFunctor X.carrier ⊤).map
      ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
        (SheafOfModules.underlyingRingSheaf (baseSheaf p))).map
        ((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
            ComplexShape.embeddingUpNat rfl).hom)).hom (globalExtend p n s) = s := by
    exact evaluation_map_extendXIso_hom_globalExtend p n s
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg ((sectionsFunctor X.carrier ⊤).map ((SheafOfModules.deRhamAbelianComplex
    (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential
      (Scheme.Hom.deRhamAlgebras p))).extendXIso ComplexShape.embeddingUpNat rfl).inv).hom h3).trans
      rfl)

/-- The cocycle `abelianCycle p n s hs` is the global form `abelianExtend p n s` in degree `n`. -/
theorem iCycles_abelianCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    ((abelianSections p).obj.iCycles n).hom (abelianCycle p n s hs) = abelianExtend p n s :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
      (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).inv).hom (n : ℤ))
    (underlyingCycle p n s hs)).trans
    ((congrArg _ (iCycles_underlyingCycle p n s hs)).trans
      (deRhamAbelianComplexPlusIso_inv_globalExtend p n s))

variable {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- **The class of the elementwise cochain of a closed global form, in the abelian realization**,
with the cocycle of the de Rham complex of abelian sheaves written out. -/
theorem classMap_restrictTot_abelianCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    (classMap p U hU n).hom ((cocycleClass n (toMor (restrictTot p U n s))
        (toMor_comp_d_eq_zero _ (restrictTot_cocycle p U hU n s hs))).hom 1) =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n).hom.hom
        (Stacks.Cech.Hypercohomology.abelianGlobalClass _ n (abelianCycle p n s hs)) :=
  classMap_restrictTot_eq p U hU n s hs _ ((congrArg _ (cyclesMap_abelianCycle p n s hs)).trans
    (iCycles_underlyingCycle p n s hs))

end Generic

section Pullback

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The pull-back of a global form** of `Ω^b_{Y/S}` to a global form of `Ω^b_{X/S}`, by the
canonical map of de Rham complexes of the square `(f, 𝟙 S)` ([Stacks, Tag 07HX]). -/
def pullbackGlobalForm (b : ℕ) (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤)) :
    ((f ≫ g).sectionsDeRhamComplex.X b).obj (op ⊤) :=
  ((Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S) (by simp)).app (b : ℤ)).val.app
    (op ⊤) σ

/-- The canonical map of de Rham complexes of abelian sheaves carries `abelianExtend g b σ` to
`abelianExtend (f ≫ g) b (pullbackGlobalForm f g b σ)`. -/
theorem pushforwardMap_abelianExtend (b : ℕ) (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤)) :
    (((sectionsFunctor Y.carrier ⊤).mapCochainComplexPlus.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus f g (f ≫ g) (𝟙 S) (by simp))).hom.f b).hom
      (abelianExtend g b σ) = abelianExtend (f ≫ g) b (pullbackGlobalForm f g b σ) := by
  have h := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
    (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} f.base)
    (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
    (Scheme.Hom.deRhamAbelianPushforwardMap f g (f ≫ g) (𝟙 S) (by simp))
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f b = b)
  have h2 := congrArg (sectionsFunctor Y.carrier ⊤).map h
  rw [Functor.map_comp, Functor.map_comp] at h2
  refine (ConcreteCategory.congr_hom h2 (abelianExtend g b σ)).trans ?_
  have h3 : ((sectionsFunctor Y.carrier ⊤).map ((SheafOfModules.deRhamAbelianComplex
      (Scheme.Hom.deRhamAlgebras g) (SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras g))).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f b = b)).hom).hom (abelianExtend g b σ) = σ :=
    Iso.inv_hom_id_apply ((sectionsFunctor Y.carrier ⊤).mapIso
      ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g))).extendXIso
          ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f b = b))) σ
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ h3).trans ?_
  exact (ConcreteCategory.comp_apply _ _ _).trans rfl

/-- The pull-back of a global form commutes with the de Rham differentials. -/
theorem d_pullbackGlobalForm (b : ℕ) (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤)) :
    ((((f ≫ g).sectionsDeRhamComplex.d b (b + 1)).app (op ⊤)).hom (pullbackGlobalForm f g b σ)) =
      pullbackGlobalForm f g (b + 1) (((g.sectionsDeRhamComplex.d b (b + 1)).app (op ⊤)).hom σ) :=
  Scheme.Hom.deRhamFormsPushforwardHom_comm_d f g (f ≫ g) (𝟙 S) (by simp) b (op ⊤) σ

/-- The pull-back of a closed global form is closed. -/
theorem pullbackGlobalForm_closed (b : ℕ) (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤))
    (hσ : ((globalSectionsComplex g).d b (b + 1)).hom (globalExtend g b σ) = 0) :
    ((globalSectionsComplex (f ≫ g)).d b (b + 1)).hom
      (globalExtend (f ≫ g) b (pullbackGlobalForm f g b σ)) = 0 := by
  rw [globalSectionsComplex_d_globalExtend_eq_zero_iff, d_pullbackGlobalForm,
    (globalSectionsComplex_d_globalExtend_eq_zero_iff g b σ).1 hσ]
  exact map_zero _

/-- **The canonical map of de Rham complexes on the cocycle of a closed global form** is the
cocycle of its pull-back. -/
theorem cyclesMap_pushforwardMap_abelianCycle (b : ℕ)
    (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤))
    (hσ : ((globalSectionsComplex g).d b (b + 1)).hom (globalExtend g b σ) = 0) :
    HomologicalComplex.cyclesMap ((sectionsFunctor Y.carrier ⊤).mapCochainComplexPlus.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus f g (f ≫ g) (𝟙 S) (by simp))).hom b
        (abelianCycle g b σ hσ) =
      abelianCycle (f ≫ g) b (pullbackGlobalForm f g b σ)
        (pullbackGlobalForm_closed f g b σ hσ) := by
  have hinj : Function.Injective ((abelianSections (f ≫ g)).obj.iCycles b).hom :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  refine hinj ?_
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((sectionsFunctor Y.carrier ⊤).mapCochainComplexPlus.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus f g (f ≫ g) (𝟙 S) (by simp))).hom (b : ℤ))
    (abelianCycle g b σ hσ)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ (iCycles_abelianCycle g b σ hσ)).trans ?_
  exact (pushforwardMap_abelianExtend f g b σ).trans (iCycles_abelianCycle _ _ _ _).symm

/-- **The pull-back of de Rham cohomology `f^* : H^k_{dR}(Y/S) ⟶ H^k_{dR}(X/S)`** of the square
`(f, 𝟙 S)` ([Stacks, Tag 0FL6]), on the module realization of de Rham cohomology (in which the cup
product lives), through the comparison of the two realizations ([Stacks, Tag 01F1]). -/
def deRhamPullbackModule (k : ℤ) :
    SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) k →+
      SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) k :=
  ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) k).inv ≫
    Scheme.Hom.deRhamCohomologyPullback f g (f ≫ g) (𝟙 S) (by simp) k ≫
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) k).hom).hom

variable {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)
  {κ : Type u} (V : κ → Y.Opens) (hV : ⊤ = ⨆ i, V i)

/-- **The pull-back of de Rham cohomology on the Čech class of a closed global form**: `f^*` of
the Čech class of the cochain `t ↦ σ|_{V_t}` of a closed global form `σ` of `Y/S` is the Čech
class of the cochain `t ↦ (f^*σ)|_{U_t}` of its pull-back. -/
theorem deRhamPullbackModule_classMap_restrictTot (b : ℕ)
    (σ : (g.sectionsDeRhamComplex.X b).obj (op ⊤))
    (hσ : ((globalSectionsComplex g).d b (b + 1)).hom (globalExtend g b σ) = 0) :
    deRhamPullbackModule f g b ((classMap g V hV b).hom ((cocycleClass b
        (toMor (restrictTot g V b σ)) (toMor_comp_d_eq_zero _
          (restrictTot_cocycle g V hV b σ hσ))).hom 1)) =
      (classMap (f ≫ g) U hU b).hom ((cocycleClass b (toMor (restrictTot (f ≫ g) U b
        (pullbackGlobalForm f g b σ))) (toMor_comp_d_eq_zero _ (restrictTot_cocycle (f ≫ g) U hU b
          (pullbackGlobalForm f g b σ) (pullbackGlobalForm_closed f g b σ hσ)))).hom 1) := by
  rw [classMap_restrictTot_abelianCycle g V hV b σ hσ,
    classMap_restrictTot_abelianCycle (f ≫ g) U hU b _ (pullbackGlobalForm_closed f g b σ hσ),
    ← cyclesMap_pushforwardMap_abelianCycle f g b σ hσ,
    ← Scheme.Hom.deRhamCohomologyPullback_abelianGlobalClass]
  show ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (b : ℤ)).hom.hom
    ((Scheme.Hom.deRhamCohomologyPullback f g (f ≫ g) (𝟙 S) (by simp) b).hom
      ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (b : ℤ)).inv.hom
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (b : ℤ)).hom.hom _)))) = _
  rw [Iso.hom_inv_id_apply]

end Pullback

section Affine

variable {Y S : Scheme.{u}} (g : Y ⟶ S) [IsAffine Y] [IsAffine S]

/-- The closed global form of `Y/S` corresponding to a form of `Ω^•_{A/R}`, `A = Γ(Y, 𝒪_Y)`,
`R = Γ(S, 𝒪_S)`, through `Γ(Y, Ω^•_{Y/S}) = Ω^•_{A/R}`. -/
def affineForm (b : ℕ) (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b) :
    (g.sectionsDeRhamComplex.X b).obj (op ⊤) :=
  ((globalComplexIso g).hom.f b).hom
    (((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex (baseMap g)).extendXIso
      ComplexShape.embeddingUpNat rfl).hom.hom ν)

set_option maxRecDepth 8000 in
/-- In degree `b`, `affineClassComplexMap g` sends a form `ν` of `Ω^•_{A/R}` to the cochain
`restrictTot g topCover b (affineForm g b ν)`. -/
theorem affineClassComplexMap_f_apply (b : ℕ)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b) :
    ((affineClassComplexMap g).f b).hom ν = restrictTot g topCover b (affineForm g b ν) := by
  refine (ConcreteCategory.congr_hom (affineClassComplexMap_f g b) ν).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact (ConcreteCategory.comp_apply _ _ _).trans rfl

/-- The global form of a cocycle of `Ω^•_{A/R}` is closed. -/
theorem affineForm_closed (b : ℕ) (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom ν = 0) :
    ((globalSectionsComplex g).d b (b + 1)).hom (globalExtend g b (affineForm g b ν)) = 0 := by
  rw [globalSectionsComplex_d_globalExtend_eq_zero_iff]
  have h1 := ConcreteCategory.congr_hom ((affineClassComplexMap g).comm b (b + 1)) ν
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hν, map_zero,
    affineClassComplexMap_f_apply, cechTot_d_apply' topCover _ (by rfl)] at h1
  calc ((g.sectionsDeRhamComplex.d b (b + 1)).app (op ⊤)).hom (affineForm g b ν)
      = ((g.sectionsDeRhamComplex.d b (b + 1)).app (op ⊤)).hom (TopCover.projX
          g.sectionsDeRhamComplex b (restrictTot g topCover b (affineForm g b ν))) :=
        congrArg _ (TopCover.projX_inclX g.sectionsDeRhamComplex b (affineForm g b ν)).symm
    _ = TopCover.projX g.sectionsDeRhamComplex (b + 1) 0 :=
        (TopCover.projX_totDTo g.sectionsDeRhamComplex b
          (restrictTot g topCover b (affineForm g b ν))).symm.trans (congrArg _ h1)
    _ = 0 := map_zero _

/-- **The class map of `Y`, on the class of a cocycle of `Ω^•_{A/R}`**, is the Čech class, for
the cover `{Y}`, of the cochain of the corresponding closed global form. -/
theorem affineClassMap_cocycleClass (b : ℕ)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom ν = 0) :
    (affineClassMap g b).hom ((cocycleClass b (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1) =
      (classMap g topCover top_eq_iSup_topCover b).hom ((cocycleClass b
        (toMor (restrictTot g topCover b (affineForm g b ν))) (toMor_comp_d_eq_zero _
          (restrictTot_cocycle g topCover top_eq_iSup_topCover b _
            (affineForm_closed g b ν hν)))).hom 1) := by
  have h := cocycleClass_affineClassMap g b (toMor ν) (toMor_comp_d_eq_zero _ hν)
  rw [Stacks.Cech.Hypercohomology.cocycleClass_congr b ((Stacks.Cech.Hypercohomology.toMor_comp _
    _).trans (congrArg toMor (affineClassComplexMap_f_apply g b ν))) _
      (toMor_comp_d_eq_zero _ (restrictTot_cocycle g topCover top_eq_iSup_topCover b _
        (affineForm_closed g b ν hν)))] at h
  exact ConcreteCategory.congr_hom h 1

end Affine

section Base

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The pull-back of a global section of `Ω^b_{Y/S}` to a global section of `Ω^b_{X/S}`. -/
def pullbackSection (b : ℕ) (σ : Γ(Scheme.Hom.relativeDifferentialForms g (b : ℤ), ⊤)) :
    Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ), ⊤) :=
  ((Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S) (by simp)).app (b : ℤ)).val.app
    (op ⊤) σ

/-- `pullbackSection` is additive. -/
theorem pullbackSection_add (b : ℕ) (σ τ : Γ(Scheme.Hom.relativeDifferentialForms g (b : ℤ), ⊤)) :
    pullbackSection f g b (σ + τ) = pullbackSection f g b σ + pullbackSection f g b τ :=
  map_add (((Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S) (by simp)).app
    (b : ℤ)).val.app (op ⊤)).hom σ τ

/-- `pullbackSection` sends `0` to `0`. -/
theorem pullbackSection_zero (b : ℕ) :
    pullbackSection f g b 0 = 0 :=
  map_zero (((Scheme.Hom.deRhamFormsPushforwardHom f g (f ≫ g) (𝟙 S) (by simp)).app
    (b : ℤ)).val.app (op ⊤)).hom

variable [IsAffine Y] [IsAffine S]

/-- **The pull-back of a global form, restricted to an affine open `V` of `X`, is the ring-level
pull-back of forms** along `Γ(Y, 𝒪_Y) ⟶ Γ(X, V)`, through the identifications of forms over
affine opens with Kähler forms. -/
theorem formsEquiv_restrict_pullbackGlobalForm {V : X.Opens} (hV : IsAffineOpen V) (b : ℕ)
    (σ : Γ(Scheme.Hom.relativeDifferentialForms g (b : ℤ), ⊤)) :
    formsEquiv (f ≫ g) hV b ((Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op (pullbackSection f g b σ)) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (baseMap g) (totalChartMap f g V)
        (chartMap f V) (baseMap_comp_chartMap f g V) b
        (formsEquiv g (isAffineOpen_top Y) b σ) := by
  induction σ using Stacks.DeRham.FormsGenerators.induction_on_affine g (isAffineOpen_top Y)
    (isAffineOpen_top S) (le_preimage_top g ⊤) with
  | h0 =>
    rw [pullbackSection_zero, (((Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op).hom).map_zero, (formsEquiv (f ≫ g) hV b).map_zero,
      (formsEquiv g (isAffineOpen_top Y) b).map_zero,
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_zero]
  | hadd x y hx hy =>
    rw [pullbackSection_add, (((Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op).hom).map_add, (formsEquiv (f ≫ g) hV b).map_add, hx, hy]
    refine (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_add _ _ _ _ b _ _).symm.trans ?_
    exact congrArg _ (map_add (formsEquiv g (isAffineOpen_top Y) b) x y).symm
  | hgen c a =>
    have h1 : pullbackSection f g b (c • Stacks.DeRham.FormsGenerators.gen g ⊤ a) =
        (f.app ⊤).hom c • Stacks.DeRham.FormsGenerators.gen (f ≫ g) (f ⁻¹ᵁ ⊤)
          (fun i => (f.app ⊤).hom (a i)) := by
      rw [pullbackSection, ← Stacks.DeRham.FormsGenerators.formsDirectImageComparison_eq]
      exact Stacks.DeRham.FormsGenerators.formsDirectImageComparison_app_smul_gen g f ⊤ c a
    have h2 := Stacks.DeRham.FormsGenerators.res_smul_gen (f ≫ g) (le_top : V ≤ f ⁻¹ᵁ ⊤)
      ((f.app ⊤).hom c) (fun i => (f.app ⊤).hom (a i))
    have h3 := Stacks.DeRham.FormsGenerators.formsSectionsIso_hom_smul_gen (f ≫ g) hV
      (isAffineOpen_top S) (le_preimage_top (f ≫ g) V)
      (X.presheaf.map (homOfLE (le_top : V ≤ f ⁻¹ᵁ ⊤)).op ((f.app ⊤).hom c))
      (fun i => X.presheaf.map (homOfLE (le_top : V ≤ f ⁻¹ᵁ ⊤)).op ((f.app ⊤).hom (a i)))
    have h4 := Stacks.DeRham.FormsGenerators.formsSectionsIso_hom_smul_gen g (isAffineOpen_top Y)
      (isAffineOpen_top S) (le_preimage_top g ⊤) c a
    refine (congrArg (formsEquiv (f ≫ g) hV b) ((congrArg _ h1).trans h2)).trans ?_
    refine h3.trans ?_
    refine Eq.trans ?_ (congrArg (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (baseMap g)
      (totalChartMap f g V) (chartMap f V) (baseMap_comp_chartMap f g V) b) h4).symm
    refine Eq.trans ?_ ((Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_smul (baseMap g)
      (totalChartMap f g V) (chartMap f V) (baseMap_comp_chartMap f g V) b c _).trans
      (congrArg _ (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_ιMulti_d (baseMap g)
        (totalChartMap f g V) (chartMap f V) (baseMap_comp_chartMap f g V) b a))).symm
    rfl

/-- The restriction to an affine open `V` of `X` of the pull-back of the global form corresponding
to a Kähler form `ν`, read through `sectionsEquiv`, is the ring-level pull-back of `ν`. -/
theorem formsEquiv_sectionsEquiv_base {V : X.Opens} (hV : IsAffineOpen V) (b : ℕ)
    (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g))) :
    formsEquiv (f ≫ g) hV b (sectionsEquiv (f ≫ g) b V ((sectionsEquiv (f ≫ g) b V).symm
      ((Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op
          (pullbackSection f g b ((formsEquiv g (isAffineOpen_top Y) b).symm ν))))) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (baseMap g) (totalChartMap f g V)
        (chartMap f V) (baseMap_comp_chartMap f g V) b ν := by
  rw [LinearEquiv.apply_symm_apply, formsEquiv_restrict_pullbackGlobalForm,
    AddEquiv.apply_symm_apply]

end Base

end AlgebraicGeometry.DeRhamKatzOdaCech

end
