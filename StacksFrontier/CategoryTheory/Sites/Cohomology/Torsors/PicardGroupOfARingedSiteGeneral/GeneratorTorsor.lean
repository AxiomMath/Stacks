module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModulesSupplement

/-!
# Local generators and their torsor, with independent universes

The local generators `Stacks.Cohomology.Torsors.Generators.GeneratorSections'` of a sheaf of
modules over a ringed site `AlgebraicGeometry.RingedSite.{u, v, w}`, their local existence for an
invertible module, the sheaf of local generators, the torsor of local generators
`Stacks.Cohomology.Torsors.Generators.generatorTorsor'` under the units, and the trivialization
of a module by a generator together with the criterion for a morphism of torsors to be an
isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u v w t

namespace Stacks.Cohomology.Torsors.Generators

/-! ### Local generators of a sheaf of modules -/

/-- The *local generators* of a sheaf of modules over an object `U` of a ringed site: the
sections over `U` by which multiplication is bijective over every arrow into `U`.

This generalizes `Stacks.Cohomology.Torsors.Generators.GeneratorSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
abbrev GeneratorSections' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :=
  {s : L.val.obj (op U) //
    ∀ (V : X.C) (f : V ⟶ U),
      Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)}

/-- Two local generators over the same object differ by a unique unit.

This generalizes `Stacks.Cohomology.Torsors.Generators.existsUnique_unit_smul_generatorSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem existsUnique_unit_smul_generatorSections'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s t : GeneratorSections' X L U) :
    ∃! a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ,
      a.val • s.val = t.val := by
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)
  let : CommRing R := inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  have hbij (u : GeneratorSections' X L U) : Function.Bijective (fun r : R => r • u.val) := by
    simpa using u.property U (𝟙 U)
  have hs := hbij s
  obtain ⟨r, hr⟩ := hs.2 t.val
  obtain ⟨q, hq⟩ := (hbij t).2 s.val
  change r • s.val = t.val at hr
  change q • t.val = s.val at hq
  have hqr : q * r = 1 := by
    apply hs.1
    calc
      (q * r) • s.val = q • (r • s.val) := by rw [mul_smul]
      _ = q • t.val := by rw [hr]
      _ = s.val := hq
      _ = 1 • s.val := (one_smul R s.val).symm
  let a : Rˣ := ⟨r, q, calc r * q = q * r := mul_comm r q
      _ = 1 := hqr, hqr⟩
  refine ⟨a, hr, ?_⟩
  intro b hb
  apply Units.ext
  apply hs.1
  calc
    b.val • s.val = t.val := hb
    _ = a.val • s.val := hr.symm

/-! ### Generators from a trivialization, and local existence -/

/-- The image of `1` under a trivialization of a module on the slice site over `U` is a local
generator over `U`.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_of_isIso_unitHom`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_of_isIso_unitHom'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (f : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ L.over U)
    (hf : IsIso f) : GeneratorSections' X L U := by
  let s := (L.over U).unitHomEquiv f
  let sU := s.val (op (Over.mk (𝟙 U)))
  have hfEq : (L.over U).unitHomEquiv.symm s = f :=
    (L.over U).unitHomEquiv.symm_apply_apply f
  refine ⟨sU, ?_⟩
  intro V g
  letI : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op V)))
  have hbij : Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ g.op sU) := by
    letI : IsIso f := hf
    have hpres : IsIso ((SheafOfModules.forget
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map f) := Functor.map_isIso
      (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) f
    have hcomp : IsIso (f.val.app (op (Over.mk g))) :=
      Functor.map_isIso
        (PresheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj
          (op (Over.mk g)))
          ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map f)
    have h := (ConcreteCategory.isIso_iff_bijective
      (f.val.app (op (Over.mk g)))).1 hcomp
    have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ g.op sU) =
        ⇑(f.val.app (op (Over.mk g))).hom := by
      have hval : ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map
          ((L.over U).unitHomEquiv.symm s)) = (L.over U).val.unitHomEquiv.symm s := by
        simp only [SheafOfModules.unitHomEquiv]
        rfl
      have hsval : s.val (op (Over.mk g)) = (L.val.map g.op).hom sU :=
        (s.property (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 U)).op).symm
      funext r
      rw [← hfEq]
      change r • (L.val.map g.op).hom sU =
        (((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).map
          ((L.over U).unitHomEquiv.symm s)).app (op (Over.mk g))).hom r
      rw [hval, ← hsval]
      simp only [PresheafOfModules.unitHomEquiv, Equiv.coe_fn_symm_mk]
      rfl
    rw [hfun]
    exact h
  exact hbij

/-- **Local existence of generators.** On a locally ringed site an invertible module has a local
generator over each member of a covering of every object; this is Stacks 0B8Q.

This generalizes `Stacks.Cohomology.Torsors.Generators.exists_cover_generatorSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem exists_cover_generatorSections'
    (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L)
    (U : X.C) :
    ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧ ∀ i, Nonempty (GeneratorSections' X L (V i)) := by
  have := hL
  have hfree :=
    AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' X L hX
  obtain ⟨I, V, f, hcover, hlocal⟩ := hfree U
  refine ⟨I, V, f, hcover, ?_⟩
  intro i
  obtain ⟨ι, ⟨hcol⟩⟩ := hlocal i
  let : IsColimit (Cofan.mk (L.over (V i)) ι) := hcol
  let : IsIso (ι 0) := cofanFinOne_inj_isIso ι hcol 0
  exact ⟨generatorSections_of_isIso_unitHom' X L (V i) (ι 0) (by infer_instance)⟩

/-- Restricting a local generator gives a local generator.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_restrict`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_restrict'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U) (s : GeneratorSections' X L U) :
    GeneratorSections' X L V := by
  refine ⟨L.val.restrictₛₗ f.op s.val, ?_⟩
  intro W g
  have h := s.property W (g ≫ f)
  have heq :
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ g.op (L.val.restrictₛₗ f.op s.val)) =
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ (g ≫ f).op s.val) := by
    funext r
    simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
    exact congrArg (fun t => r • t) (L.val.map_comp_apply f.op g.op s.val).symm
  rw [heq]
  exact h

/-- The restrictions of a module section to all objects of the slice form a section of the
relocalized module.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_overSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_overSections'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U)) : (L.over U).val.sections := by
  refine PresheafOfModules.sectionsMk (fun Y => L.val.restrictₛₗ Y.unop.hom.op s) ?_
  intro Y Z f
  change L.val.map f.unop.left.op (L.val.map Y.unop.hom.op s) = L.val.map Z.unop.hom.op s
  rw [← L.val.map_comp_apply, ← op_comp, Over.w f.unop]

/-- The morphism out of the unit module attached to a section is multiplication by that
section.

This generalizes `Stacks.Cohomology.Torsors.Generators.unitHom_symm_app_smul`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem unitHom_symm_app_smul'
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    (s : M.sections) (V : Dᵒᵖ) (a : (R.obj.obj V : Type w)) :
    (ConcreteCategory.hom ((M.unitHomEquiv.symm s).val.app V)) a =
      ((LinearMap.ringLmapEquivSelf (R.obj.obj V) ℤ (M.val.obj V)).symm (s.eval V)) a := by
  simp only [SheafOfModules.unitHomEquiv, PresheafOfModules.unitHomEquiv]
  rfl

/-- **A section which generates locally generates.** If a section over `U` generates after
restriction along the members of a covering of `U`, it is a local generator over `U`.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_of_locally_generator`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_of_locally_generator'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U))
    (S : Sieve U) (hS : S ∈ X.J U)
    (hlocal : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∀ (W : X.C) (g : W ⟶ V), Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
          r • L.val.restrictₛₗ (g ≫ f).op s)) :
    GeneratorSections' X L U := by
  let U₀ : Over U := Over.mk (𝟙 U)
  let S' : Sieve U₀ := (Sieve.overEquiv U₀).symm S
  have hS' : S' ∈ (X.J.over U) U₀ := X.J.overEquiv_symm_mem_over U₀ S hS
  let M := L.over U
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
  let N := SheafOfModules.unit R
  let sec := generatorSections_overSections' X L U s
  let f : N ⟶ M := M.unitHomEquiv.symm sec
  let F := (SheafOfModules.toSheaf R).obj N
  let G := (SheafOfModules.toSheaf R).obj M
  have hF : Presheaf.IsSheaf (X.J.over U) (F.obj ⋙ forget AddCommGrpCat.{w}) :=
    Presheaf.isSheaf_comp_of_isSheaf (X.J.over U) F.obj (forget AddCommGrpCat.{w}) F.property
  have hG : Presheaf.IsSheaf (X.J.over U) (G.obj ⋙ forget AddCommGrpCat.{w}) :=
    Presheaf.isSheaf_comp_of_isSheaf (X.J.over U) G.obj (forget AddCommGrpCat.{w}) G.property
  let φ : (F.obj ⋙ forget AddCommGrpCat.{w}) ⟶ (G.obj ⋙ forget AddCommGrpCat.{w}) :=
    Functor.whiskerRight ((SheafOfModules.toSheaf R).map f).hom (forget AddCommGrpCat.{w})
  have hform (V : Over U) (r : (R.obj.obj (op V) : Type w)) :
      φ.app (op V) r = r • sec.eval (op V) := by
    change (ConcreteCategory.hom (f.val.app (op V))) r = r • sec.eval (op V)
    rw [unitHom_symm_app_smul' (X.J.over U) M sec (op V) r]
    simp [LinearMap.ringLmapEquivSelf]
  have hφ : ∀ ⦃V : Over U⦄ (g : V ⟶ U₀), S' g →
      Function.Bijective (φ.app (op V)) := by
    intro V g hg
    have hbase : S g.left := (Sieve.overEquiv_symm_iff S g).mp hg
    have hV : V.hom = g.left := by simpa [U₀] using (Over.w g).symm
    let t : GeneratorSections' X L V.left := by
      refine ⟨L.val.restrictₛₗ g.left.op s, ?_⟩
      intro W k
      have heq :
          (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ k.op (L.val.restrictₛₗ g.left.op s)) =
          (fun r => r • L.val.restrictₛₗ (k ≫ g.left).op s) := by
        funext r
        simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
        exact congrArg (fun z => r • z) (L.val.map_comp_apply g.left.op k.op s).symm
      rw [heq]
      exact hlocal g.left hbase W k
    have hgen : Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.left) =>
          r • t.val) := by
      simpa using t.property V.left (𝟙 V.left)
    have htval : t.val = sec.eval (op V) := by
      change L.val.map g.left.op s = L.val.map V.hom.op s
      rw [hV]
    letI : Module (R.obj.obj (op V) : Type w) (M.val.obj (op V) : Type w) :=
      (L.val.obj (op V.left)).isModule
    have hgenSec : Function.Bijective
        (fun r : (R.obj.obj (op V) : Type w) => r • sec.eval (op V)) := by
      convert hgen using 1
      · rfl
      · rfl
      · rw [htval]
        exact HEq.rfl
    have hfun : ⇑(φ.app (op V)) =
        (fun r : (R.obj.obj (op V) : Type w) => r • sec.eval (op V)) := funext (hform V)
    rw [hfun]
    exact hgenSec
  have hbij : ∀ (T : Over U), Function.Bijective (φ.app (op T)) := by
    intro T
    let p : T ⟶ U₀ := Over.homMk T.hom (by simp [U₀])
    let Rcover : Sieve T := S'.pullback p
    have hRcover : Rcover ∈ (X.J.over U) T := (X.J.over U).pullback_stable _ hS'
    exact bijective_of_bijective_on_cover (X.J.over U) hF hG
      Rcover hRcover φ (fun V g hg => hφ (g ≫ p) hg)
  refine ⟨s, ?_⟩
  intro V g
  let qV : Over U := Over.mk g
  have hqV : Function.Bijective (φ.app (op qV)) := hbij qV
  letI : Module (R.obj.obj (op qV) : Type w) ((L.over U).val.obj (op qV) : Type w) :=
    ((L.over U).val.obj (op qV)).isModule
  letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w)
      (L.val.obj (op V) : Type w) :=
    (L.val.obj (op V)).isModule
  letI : Module (R.obj.obj (op qV) : Type w) (L.val.obj (op V) : Type w) :=
    (L.val.obj (op V)).isModule
  change Function.Bijective
    (fun r : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w) =>
      r • (L.val.restrictₛₗ g.op s : L.val.obj (op V)))
  have hfun : ⇑(ConcreteCategory.hom (φ.app (op qV))) =
      (fun r : (R.obj.obj (op qV) : Type w) => r • sec.eval (op qV)) := funext (hform qV)
  have hsec : sec.eval (op qV) = L.val.restrictₛₗ g.op s := rfl
  have hgenSlice : Function.Bijective
      (fun r : (R.obj.obj (op qV) : Type w) => r • sec.eval (op qV)) := by
    change Function.Bijective (⇑(ConcreteCategory.hom (φ.app (op qV))))
    rw [hfun]
    exact hqV
  convert hgenSlice using 1
  · rfl
  · rfl
  · rw [← hsec]
    exact HEq.rfl

/-! ### The sheaf of local generators -/

/-- The local generators as a subfunctor of the underlying presheaf of sets of a module.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSectionsSubfunctor`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSectionsSubfunctor'
    (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Subfunctor (L.val.presheaf ⋙ forget AddCommGrpCat) where
  obj U := {s | ∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
    (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
      r • L.val.restrictₛₗ f.op s)}
  map := by
    intro U V f s hs
    change ∀ (W : X.C) (g : W ⟶ V.unop), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ g.op (L.val.map f s))
    intro W g
    have heq :
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
          r • L.val.restrictₛₗ g.op (L.val.map f s)) =
        (fun r => r • L.val.restrictₛₗ (g ≫ f.unop).op s) := by
      funext r
      simp only [op_comp]
      exact congrArg (fun z => r • z) (L.val.map_comp_apply f g.op s).symm
    rw [heq]
    exact hs W (g ≫ f.unop)

/-- The sheaf of local generators of a sheaf of modules. Its sheaf condition is exactly the
statement that a section which generates locally generates.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSectionsSheaf`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSectionsSheaf'
    (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf X.J (Type w) := by
  let G := generatorSectionsSubfunctor' X L
  have hbase : Presieve.IsSheaf X.J (L.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type X.J _).1
      (Presheaf.isSheaf_comp_of_isSheaf X.J L.val.presheaf (forget AddCommGrpCat) L.isSheaf)
  have hG : Presieve.IsSheaf X.J G.toFunctor := by
    rw [Subfunctor.isSheaf_iff (G := G) hbase]
    intro U s hs
    change ∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)
    simpa only [generatorSections_of_locally_generator'] using
      (generatorSections_of_locally_generator' X L U.unop s (G.sieveOfSection s) hs (by
        intro V f hf W g
        have hmem : L.val.presheaf.map f.op s ∈ G.obj (op V) := hf
        have hbij := hmem W g
        have hmap : (ConcreteCategory.hom (L.val.presheaf.map f.op)) s =
            L.val.restrictₛₗ f.op s := rfl
        rw [hmap] at hbij
        have heq :
            (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
              r • L.val.restrictₛₗ g.op (L.val.restrictₛₗ f.op s)) =
            (fun r => r • L.val.restrictₛₗ (g ≫ f).op s) := by
          funext r
          simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
          exact congrArg (fun z => r • z) (L.val.map_comp_apply f.op g.op s).symm
        simpa only [← heq] using hbij)).property
  exact ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type X.J _).2 hG⟩

/-- A unit multiple of a local generator is a local generator.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_smul_unit`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_smul_unit'
    (X : RingedSite.{u, v, w}) (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ)
    (s : GeneratorSections' X L U) : GeneratorSections' X L U := by
  letI : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  refine ⟨@SMul.smul _ _ _ a.val s.val, ?_⟩
  intro V g
  letI : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op V)))
  let aV : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w)ˣ :=
    Units.map ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op).hom.toMonoidHom a
  let sV := L.val.restrictₛₗ g.op s.val
  have ha : L.val.restrictₛₗ g.op (@SMul.smul _ _ _ a.val s.val) =
      @SMul.smul _ _ _ aV.val sV := by
    change L.val.restrictₛₗ g.op (a.val • s.val) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op).hom a.val •
        L.val.restrictₛₗ g.op s.val
    exact (L.val.restrictₛₗ g.op).map_smulₛₗ a.val s.val
  have hs := s.property V g
  constructor
  · intro x y hxy
    have hxy0 : x • L.val.restrictₛₗ g.op (a.val • s.val) =
        y • L.val.restrictₛₗ g.op (a.val • s.val) := hxy
    have hxy' : (x * aV.val) • sV = (y * aV.val) • sV := calc
      (x * aV.val) • sV = x • (aV.val • sV) := by rw [mul_smul]
      _ = x • L.val.restrictₛₗ g.op (a.val • s.val) := congrArg (fun q => x • q) ha.symm
      _ = y • L.val.restrictₛₗ g.op (a.val • s.val) := hxy0
      _ = y • (aV.val • sV) := congrArg (fun q => y • q) ha
      _ = (y * aV.val) • sV := by rw [mul_smul]
    exact (Units.mul_left_inj aV).1 (hs.1 hxy')
  · intro t
    obtain ⟨z, hz⟩ := hs.2 t
    refine ⟨z * aV⁻¹, ?_⟩
    change (z * aV⁻¹) • L.val.restrictₛₗ g.op (@SMul.smul _ _ _ a.val s.val) = t
    rw [ha]
    calc
      (z * aV⁻¹) • (aV.val • sV) = ((z * aV⁻¹) * aV.val) • sV := by rw [← mul_smul]
      _ = z • sV := by simp [mul_assoc]
      _ = t := hz

/-! ### The torsor of local generators -/

/-- A torsor under the units together with the identification of its sections with the local
generators of a module, the compatibility of that identification with restriction, and the
statement that a unit acts by multiplication.

This generalizes `Stacks.Cohomology.Torsors.Generators.GeneratorTorsor`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
structure GeneratorTorsor' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  /-- The torsor under the additive notation for the units sheaf. -/
  torsor : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)
  /-- Sections are precisely local generators. -/
  sectionsEquiv (U : X.Cᵒᵖ) : torsor.1.presheaf.obj U ≃ GeneratorSections' X L U.unop
  /-- Restriction of torsor sections agrees with restriction of module sections. -/
  sectionsEquiv_restrict {U V : X.Cᵒᵖ} (f : U ⟶ V) (s : torsor.1.presheaf.obj U) :
    (sectionsEquiv V (torsor.1.presheaf.map f s)).val =
      L.val.restrictₛₗ f (sectionsEquiv U s).val
  /-- The action of a unit is multiplication on the corresponding generator. -/
  sectionsEquiv_smul (U : X.Cᵒᵖ) (a : (X.O.obj.obj U)ˣ) (s : torsor.1.presheaf.obj U) :
    (sectionsEquiv U (torsor.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s)).val =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (L.val.obj U) _ a.val
        (sectionsEquiv U s).val

/-- **The generator torsor of an invertible module.** On a locally ringed site the local
generators of an invertible module form a torsor under the sheaf of units.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsor`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorTorsor' (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    GeneratorTorsor' X L := by
  let H := unitsAddSheaf X
  let G := Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf H
  let F : PseudoTorsor G := {
    presheaf := (generatorSectionsSheaf' X L).obj
    isSheaf := (generatorSectionsSheaf' X L).property
    act := by
      intro U a s
      change GeneratorSections' X L U.unop at s
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)
          (L.val.obj U : Type w) :=
        (L.val.obj U).isModule
      exact generatorSections_smul_unit' X L U.unop
        (Additive.toMul (Multiplicative.toAdd a)) s
    one_act := by
      intro U s
      change GeneratorSections' X L U.unop at s
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)
          (L.val.obj U : Type w) :=
        (L.val.obj U).isModule
      apply Subtype.ext
      change (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)) • s.val = s.val
      simp
    mul_act := by
      intro U a b s
      change Multiplicative (Additive ((X.O.obj.obj U : Type w)ˣ)) at a b
      change GeneratorSections' X L U.unop at s
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)
          (L.val.obj U : Type w) :=
        (L.val.obj U).isModule
      apply Subtype.ext
      let ua : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ :=
        Additive.toMul (Multiplicative.toAdd a)
      let ub : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ :=
        Additive.toMul (Multiplicative.toAdd b)
      let uab : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ :=
        Additive.toMul (Multiplicative.toAdd (a * b))
      change uab.val • s.val = ua.val • (ub.val • s.val)
      have hab : uab = ua * ub := rfl
      rw [hab, Units.val_mul, mul_smul]
    naturality := by
      intro U V f a s
      change Multiplicative (Additive ((X.O.obj.obj U : Type w)ˣ)) at a
      change GeneratorSections' X L U.unop at s
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)
          (L.val.obj U : Type w) :=
        (L.val.obj U).isModule
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V : Type w)
          (L.val.obj V : Type w) :=
        (L.val.obj V).isModule
      let ua : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ :=
        Additive.toMul (Multiplicative.toAdd a)
      let uaV : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V : Type w)ˣ :=
        Units.map ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.unop.op).hom.toMonoidHom
          ua
      apply Subtype.ext
      change (L.val.restrictₛₗ f.unop.op) (ua.val • s.val) =
        uaV.val • (L.val.restrictₛₗ f.unop.op s.val)
      rw [(L.val.restrictₛₗ f.unop.op).map_smulₛₗ]
      congr 1
    simplyTransitive := by
      intro U _ s t
      change GeneratorSections' X L U.unop at s t
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)
          (L.val.obj U : Type w) :=
        (L.val.obj U).isModule
      obtain ⟨a, ha, huniq⟩ := existsUnique_unit_smul_generatorSections' X L U.unop s t
      let E : G.presheaf.obj U ≃
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ := {
        toFun := fun b => Additive.toMul (Multiplicative.toAdd b)
        invFun := fun b => Multiplicative.ofAdd (Additive.ofMul b)
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
      refine ⟨E.symm a, ?_, ?_⟩
      · apply Subtype.ext
        change (E (E.symm a)).val • s.val = t.val
        rw [E.apply_symm_apply]
        exact ha
      · intro b hb
        have hval : E b = a := huniq (E b) (by
          change generatorSections_smul_unit' X L U.unop (E b) s = t at hb
          change (E b).val • s.val = t.val
          exact congrArg Subtype.val hb)
        exact E.eq_symm_apply.2 hval
  }
  have hF : F.IsTorsor := by
    intro U
    obtain ⟨I, V, f, hcover, hgen⟩ := exists_cover_generatorSections' X hX L hL U
    refine ⟨Sieve.ofArrows V f, hcover, ?_⟩
    intro W g hg
    obtain ⟨i, k, hk⟩ := Sieve.ofArrows.exists hg
    obtain ⟨s⟩ := hgen i
    exact ⟨generatorSections_restrict' X L k s⟩
  refine ⟨⟨F, hF⟩, fun U => Equiv.refl _, ?_, ?_⟩
  · intro U V f s
    rfl
  · intro U a s
    rfl

/-! ### Trivialization from a generator, and isomorphisms of torsors -/

/-- The morphism out of the unit module determined by a section of a module on a slice site
acts by multiplication by that section.

This generalizes `Stacks.Cohomology.Torsors.Generators.unitHomEquiv_symm_app_smul`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem unitHomEquiv_symm_app_smul' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (sec : (L.over U).val.sections)
    (V : (Over U)ᵒᵖ) (r : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj V) :
    (((L.over U).unitHomEquiv.symm sec).val.app V).hom r = r • sec.eval V := by
  rw [unitHom_symm_app_smul' (X.J.over U) (L.over U) sec V r]
  simp [LinearMap.ringLmapEquivSelf]

/-- The morphism from the unit module to a module on the slice site over `U` determined by a
local generator over `U`.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorUnitHom`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorUnitHom' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ L.over U :=
  (L.over U).unitHomEquiv.symm (generatorSections_overSections' X L U s.val)

/-- The morphism determined by a local generator is an isomorphism over every object of the
slice site, because the generator generates over every arrow.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorUnitHom_isIso_app`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorUnitHom_isIso_app' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U)
    (V : (Over U)ᵒᵖ) : IsIso ((generatorUnitHom' X L U s).val.app V) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have he : ⇑((generatorUnitHom' X L U s).val.app V).hom =
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left) =>
        r • L.val.restrictₛₗ V.unop.hom.op s.val) := by
    funext r
    exact unitHomEquiv_symm_app_smul' X L U (generatorSections_overSections' X L U s.val) V r
  rw [he]
  exact s.property V.unop.left V.unop.hom

/-- A local generator over `U` trivializes the module on the slice site over `U`.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSectionTrivialization`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSectionTrivialization' (X : RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ≅ L.over U :=
  letI (V : (Over U)ᵒᵖ) : IsIso ((generatorUnitHom' X L U s).val.app V) :=
    generatorUnitHom_isIso_app' X L U s V
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (M₁ := (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).val)
      (M₂ := (L.over U).val)
      (fun V => asIso ((generatorUnitHom' X L U s).val.app V))
      (fun {_ _} g => (generatorUnitHom' X L U s).val.naturality g))

/-- A morphism of pseudo-torsors is bijective on the sections over an object which has one.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorHom_bijective_of_nonempty`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
theorem torsorHom_bijective_of_nonempty'
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {G : SheafOfGroups.{w} J} {F F' : PseudoTorsor G}
    (e : F.Hom F') (U : Dᵒᵖ) (s₀ : F.presheaf.obj U) :
    Function.Bijective (e.hom.app U) := by
  constructor
  · intro s t h
    obtain ⟨a, ha, _⟩ := F.simplyTransitive U ⟨s⟩ s t
    have hg : F'.act U a (e.hom.app U s) = e.hom.app U s :=
      (e.map_act U a s).symm.trans ((congrArg (fun z => e.hom.app U z) ha).trans h.symm)
    have ha1 : a = 1 := (F'.simplyTransitive U ⟨e.hom.app U s⟩
      (e.hom.app U s) (e.hom.app U s)).unique hg (F'.one_act U _)
    simpa only [ha1, F.one_act] using ha
  · intro t
    obtain ⟨a, ha, _⟩ := F'.simplyTransitive U ⟨e.hom.app U s₀⟩ (e.hom.app U s₀) t
    exact ⟨F.act U a s₀, (e.map_act U a s₀).trans ha⟩

/-- Every morphism out of a torsor is an isomorphism.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorHom_isIso`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
theorem torsorHom_isIso'
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {G : SheafOfGroups.{w} J} {F F' : PseudoTorsor G}
    (hF : F.IsTorsor) (e : F.Hom F') : e.IsIso := by
  show IsIso e.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  obtain ⟨S, hS, hs⟩ := hF U.unop
  exact bijective_of_bijective_on_cover J F.isSheaf F'.isSheaf S hS e.hom (by
    intro V f hf
    obtain ⟨s⟩ := hs hf
    exact torsorHom_bijective_of_nonempty' e (op V) s)

end Stacks.Cohomology.Torsors.Generators

end
