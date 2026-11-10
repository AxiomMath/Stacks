module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StronglyCartesian
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme

/-!
# The stack of finitely generated quasi-coherent modules

The quasi-coherent modules of finite type on the schemes of the big fppf site over `S` form a
full subcategory of the category of quasi-coherent modules of Stacks 04U2, and the projection
of that subcategory to the big fppf site of `S` is again a stack: finite type is preserved by
pullback and descends along fppf coverings.

## Main definitions

* `Stacks.QCoh.isFiniteType`: the property of a quasi-coherent pair that its module is of
  finite type.
* `Stacks.QCoh.FiniteType`: the full subcategory of quasi-coherent pairs of finite type.
* `Stacks.QCoh.finiteTypeProjection`: its projection to the big fppf site over `S`.

## Main results

* `Stacks.QCoh.isStack_finiteTypeProjection`, Stacks 04U4: that projection is a stack.

## Implementation notes

The statement that the projection from *all* quasi-coherent modules is a stack (Stacks 03YM)
is not available in this library, so it is carried as a hypothesis; the content proved here is
the passage from that stack to its finite-type full subcategory, which is the content of the
source's lemma. The two conditions of Stacks 04TU are verified with the characterisation of the
strongly cartesian arrows of Stacks 04U3 together with, respectively, the stability of finite
type under pullback (Stacks 01B6) and its fppf descent (Stacks 05AZ).

The covering appearing in condition (3) is a sieve in the slice over `S`; it is replaced by a
covering family of the chosen bounded system of the big fppf site refining it, which is then
pushed to a genuine fppf covering of the underlying scheme so that Stacks 05AZ applies.

## References

* [Stacks Project, Tag 04U4](https://stacks.math.columbia.edu/tag/04U4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u v₁ u₁ v₂ u₂

/-- A cartesian arrow is cartesian over the image of itself. -/
private lemma isCartesian_map_of_isCartesian {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂}
    [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) {R T : 𝒮} {a b : 𝒳} {f : R ⟶ T} {m : a ⟶ b}
    (ha : p.obj a = R) (hb : p.obj b = T) (hm : p.IsCartesian f m) :
    p.IsCartesian (p.map m) m := by
  revert f hm
  cases ha
  cases hb
  intro f hm
  let := hm
  rw [← IsHomLift.eq_of_isHomLift p f m]
  exact hm

/-! ### Finite type under pullback and isomorphism -/

/-- If the pullback of a module along `f` is of finite type, so is its pullback along any
composite `g ≫ f`. -/
private lemma isFiniteType_pullback_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : X.Modules) (hM : ((Scheme.Modules.pullback f).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback (g ≫ f)).obj M).IsFiniteType :=
  AlgebraicGeometry.isFiniteType_of_iso ((Scheme.Modules.pullbackComp g f).app M)
    (Stacks.Modules.isFiniteType_pullback g _ hM)

/-! ### Refining a covering sieve by a chosen covering family -/

/-- A covering sieve of the big fppf site is refined by one of the site's chosen covering
families. -/
private lemma exists_isCovering_presieve₀_le (B : AlgebraicGeometry.BigFppfSite.{u})
    {X : B.Schemes} {R : Sieve X} (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [AlgebraicGeometry.BigFppfSite.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      refine ⟨E, hE, ?_⟩
      rw [hEq]
      exact Sieve.le_generate _
  | top X =>
      exact ⟨PreZeroHypercover.singleton (𝟙 X), B.coverings_isSite.1 (𝟙 X), by
        intro Y f hf
        trivial⟩
  | pullback X R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := B.coverings_isSite.2.2 ⟨X, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive X R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose F hF hFle using hlocal
      let EF := E.bind F
      have hEF : B.IsCovering ⟨X, EF⟩ :=
        B.coverings_isSite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl)
      refine ⟨EF, hEF, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      change Q ((F i).f j ≫ E.f i)
      exact hFle i _ _ ⟨j⟩

/-! ### The stack of finite-type quasi-coherent modules -/

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of a quasi-coherent pair over `S` that its module is of finite type. -/
public abbrev isFiniteType : ObjectProperty (Object B S hS) :=
  fun X ↦ X.module.IsFiniteType

/-- Quasi-coherent modules of finite type on the schemes of the big fppf site over `S`. -/
public abbrev FiniteType := (isFiniteType B S hS).FullSubcategory

/-- The projection from finite-type quasi-coherent modules to the big fppf site over `S`. -/
public noncomputable abbrev finiteTypeProjection :
    FiniteType B S hS ⥤ AlgebraicGeometry.BigFppfOver B S hS :=
  Functor.restrict (projection (B := B) (S := S) (hS := hS)) (isFiniteType B S hS)

/-- The comparison map of a strongly cartesian arrow over its own image is an isomorphism. -/
private lemma isIso_homEquivPullbackHom_snd {y x : Object B S hS} (m : y ⟶ x)
    [(projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m] :
    IsIso (homEquivPullbackHom y x m).2 :=
  (isStronglyCartesian_iff (m := m)).1 inferInstance

/-- If `m : y ⟶ x` is strongly cartesian over its own image and `x` is of finite type, so is
`y`. -/
private lemma isFiniteType_of_isStronglyCartesian {y x : Object B S hS} (m : y ⟶ x)
    [(projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m]
    (hx : x.module.IsFiniteType) : y.module.IsFiniteType :=
  have := isIso_homEquivPullbackHom_snd B S hS m
  AlgebraicGeometry.isFiniteType_of_iso (asIso (homEquivPullbackHom y x m).2)
    (Stacks.Modules.isFiniteType_pullback _ _ hx)

/-- An object of the quasi-coherent category isomorphic over the identity to one of finite
type is itself of finite type. -/
private lemma isFiniteType_of_isoOverId {A : Object B S hS}
    (hA : Functor.IsoOverId (projection (B := B) (S := S) (hS := hS)) (isFiniteType B S hS) A) :
    A.module.IsFiniteType := by
  obtain ⟨C, hC, e, he⟩ := hA
  let : (projection (B := B) (S := S) (hS := hS)).IsHomLift (𝟙 _) e.hom := he
  let : IsIso e.hom := e.isIso_hom
  exact isFiniteType_of_isStronglyCartesian B S hS e.hom hC

/-- **Stacks 04U4.** The quasi-coherent modules of finite type over `S` form a stack for the
big fppf topology: finite type is preserved by the pullbacks computing the strongly cartesian
arrows of Stacks 04U3, and it descends along fppf coverings by Stacks 05AZ, so Stacks 04TU
applies to the full subcategory they cut out. The hypothesis is Stacks 03YM, that the
projection from all quasi-coherent modules is a stack. -/
@[stacks 04U4 "conditional on Stacks 03YM, that the projection from quasi-coherent modules \
to the big fppf site of S is a stack"]
public theorem isStack_finiteTypeProjection
    (hp : Functor.IsStack (projection (B := B) (S := S) (hS := hS))
      (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    Functor.IsStack (finiteTypeProjection B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  classical
  let p := projection (B := B) (S := S) (hS := hS)
  let P : ObjectProperty (Object B S hS) := isFiniteType B S hS
  refine Functor.IsStack.fullSubcategory p _ hp P ?_ ?_
  · intro V U y x f phi hphi hx
    let : p.IsStronglyCartesian f phi := hphi
    have : p.IsStronglyCartesian (p.map phi) phi := by
      subst_hom_lift p f phi
      infer_instance
    exact Functor.isoOverId_of_prop (p := p) (P := P)
      (isFiniteType_of_isStronglyCartesian B S hS phi hx)
  · let : p.IsPreFibered := hp.isFibered.toIsPreFibered
    intro U ι Ui fi hcov x hx
    revert ι Ui fi hcov hx
    rcases x with ⟨xObj, hxbase⟩
    cases hxbase
    intro ι Ui fi hcov hx
    let U := p.obj xObj
    let x : p.Fiber (p.obj xObj) := ⟨xObj, rfl⟩
    let T := (AlgebraicGeometry.BigFppfOver.forget B S hS).obj U
    let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
    have hbase : p.obj xObj = xObj.base := d.projection_obj xObj
    have hRbase :
        Sieve.overEquiv U (Sieve.generate (Presieve.ofArrows Ui fi)) ∈ B.topology T := by
      rw [AlgebraicGeometry.BigFppfOver.topology, GrothendieckTopology.mem_over_iff] at hcov
      exact hcov
    obtain ⟨E, hE, hER⟩ := exists_isCovering_presieve₀_le B hRbase
    -- The chosen family, pushed into schemes and transported along the identification of the
    -- projection with the base, is an fppf covering of the underlying scheme of `xObj`.
    let X₀ := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
    let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj xObj.base
    let e : X₀ ≅ X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapIso (eqToIso hbase)
    have hEfp₀ : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage X₀ := by
      simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
        PreZeroHypercover.presieve₀_map, X₀, T, U,
        AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget] using
        B.isFppfCovering_of_isCovering hE
    have heCover : Presieve.singleton e.hom ∈ Scheme.fppfPrecoverage X := by
      let : Precoverage.HasIsos Scheme.fppfPrecoverage := ⟨by
        intro Y Z f hf
        let : IsIso f := hf
        exact Scheme.Hom.singleton_mem_fppfPrecoverage f⟩
      exact Precoverage.HasIsos.mem_coverings_of_isIso e.hom
    have hEfp : Presieve.ofArrows
        (fun j : Σ _ : Unit, E.I₀ ↦ B.inclusion.obj (E.X j.2))
        (fun j ↦ B.inclusion.map (E.f j.2) ≫ e.hom) ∈ Scheme.fppfPrecoverage X := by
      simpa using (Precoverage.comp_mem_coverings (J := Scheme.fppfPrecoverage)
        (f := fun _ : Unit ↦ e.hom)
        (by simp [Presieve.ofArrows_pUnit, heCover])
        (σ := fun _ : Unit ↦ E.I₀)
        (Y := fun _ j ↦ B.inclusion.obj (E.X j))
        (g := fun _ j ↦ B.inclusion.map (E.f j)) (fun _ ↦ hEfp₀))
    -- Each pullback of `xObj` along the given covering family is of finite type, hence so is
    -- each pullback along the refining family.
    have hfinitePull (i : ι) :
        ((Scheme.Modules.pullback (Object.schemeMap
          (homEquivPullbackHom (p.pullbackFiber x (fi i)).1 x.1
            (Functor.IsPreFibered.pullbackMap x.2 (fi i))).1)).obj x.1.module).IsFiniteType := by
      let y := (p.pullbackFiber x (fi i)).1
      let m := Functor.IsPreFibered.pullbackMap x.2 (fi i)
      let q := homEquivPullbackHom y x.1 m
      have : p.IsFibered := hp.isFibered
      have : p.IsCartesian (p.map m) m :=
        isCartesian_map_of_isCartesian p
          (IsHomLift.domain_eq p (fi i) m) (IsHomLift.codomain_eq p (fi i) m)
          (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 (fi i))
      have : p.IsStronglyCartesian (p.map m) m :=
        Functor.IsFibered.isStronglyCartesian_of_isCartesian p (p.map m) m
      have : IsIso q.2 := isIso_homEquivPullbackHom_snd B S hS m
      exact AlgebraicGeometry.isFiniteType_of_iso (asIso q.2).symm
        (isFiniteType_of_isoOverId B S hS (hx i))
    have hfiniteE (j : E.I₀) :
        ((Scheme.Modules.pullback (B.inclusion.map (E.f j) ≫ e.hom)).obj
          xObj.module).IsFiniteType := by
      have hEarr : E.presieve₀ (E.f j) := ⟨j⟩
      have hj := hER _ _ hEarr
      change (Sieve.generate (Presieve.ofArrows Ui fi)).arrows.functorPushforward
        (AlgebraicGeometry.BigFppfOver.forget B S hS) (E.f j) at hj
      rcases hj with ⟨Z, g, h, hg, hfac⟩
      change ∃ (Y : AlgebraicGeometry.BigFppfOver B S hS) (k : Z ⟶ Y)
        (l : Y ⟶ U), Presieve.ofArrows Ui fi l ∧ k ≫ l = g at hg
      obtain ⟨Y, k, l, hgen, hkl⟩ := hg
      obtain ⟨i, hY, hfi⟩ := Presieve.ofArrows_surj fi l hgen
      subst Y
      subst l
      rw [← hkl] at hfac
      let y := (p.pullbackFiber x (fi i)).1
      let m := Functor.IsPreFibered.pullbackMap x.2 (fi i)
      let q := homEquivPullbackHom y xObj m
      have hdom : p.obj y = Ui i := IsHomLift.domain_eq p (fi i) m
      have hybase : p.obj y = y.base := d.projection_obj y
      have hqbase : p.map m = eqToHom hybase ≫ q.1 ≫ eqToHom hbase.symm := by
        change p.map m = eqToHom hybase ≫
          ((Equiv.cast (d.hom_type y xObj)) m).1 ≫ eqToHom hbase.symm
        exact d.projection_map m
      have hmap : p.map m = eqToHom hdom ≫ fi i ≫
          eqToHom (IsHomLift.codomain_eq p (fi i) m).symm :=
        IsHomLift.fac' p (fi i) m
      have hfiq : fi i ≫ eqToHom hbase = eqToHom hdom.symm ≫ eqToHom hybase ≫ q.1 := by
        calc
          fi i ≫ eqToHom hbase = eqToHom hdom.symm ≫ p.map m ≫ eqToHom hbase := by
            rw [hmap]
            simp
          _ = eqToHom hdom.symm ≫ eqToHom hybase ≫ q.1 := by
            rw [hqbase]
            simp
      let g' : (B.inclusion.obj (E.X j)) ⟶
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj y.base :=
          B.inclusion.map (h ≫ (AlgebraicGeometry.BigFppfOver.forget B S hS).map k) ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (eqToHom hdom.symm ≫ eqToHom hybase)
      have hfacS : B.inclusion.map (E.f j) =
          B.inclusion.map (h ≫ (AlgebraicGeometry.BigFppfOver.forget B S hS).map k) ≫
            B.inclusion.map ((AlgebraicGeometry.BigFppfOver.forget B S hS).map (fi i)) := by
        rw [hfac]
        simp [Category.assoc]
      have hstep := congrArg (fun t ↦ B.inclusion.map (h ≫
          (AlgebraicGeometry.BigFppfOver.forget B S hS).map k) ≫ t)
        (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map hfiq)
      have hfactor : B.inclusion.map (E.f j) ≫ e.hom =
          g' ≫ Object.schemeMap q.1 := by
        rw [hfacS]
        simpa [g', e, Object.schemeMap,
          AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
          Functor.map_comp, Category.assoc] using hstep
      rw [hfactor]
      exact isFiniteType_pullback_comp (Object.schemeMap q.1) g' xObj.module (hfinitePull i)
    exact Functor.isoOverId_of_prop (p := p) (P := P)
      (AlgebraicGeometry.isFiniteType_of_pullback_fpqc (X := X) xObj.module xObj.quasicoherent
        (fun j : Σ _ : Unit, E.I₀ ↦ B.inclusion.obj (E.X j.2))
        (fun j ↦ B.inclusion.map (E.f j.2) ≫ e.hom)
        (by simpa using Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hEfp)
        (fun j ↦ hfiniteE j.2))

end Stacks.QCoh

end
