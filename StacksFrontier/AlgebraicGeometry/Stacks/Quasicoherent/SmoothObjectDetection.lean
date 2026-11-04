module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleClosure

/-!
# Quasi-coherent modules on an algebraic stack are detected on smooth objects

Let `𝒳` be an algebraic stack over `S`. An object `x` of `𝒳` is *smooth* when the 1-morphism
`x : U → 𝒳` it names out of the scheme it lies over is smooth (the objects of the lisse-étale
site of **Stacks 0787**). This file proves that a morphism of quasi-coherent modules on the fppf
site of `𝒳` which is bijective on the sections over every smooth object is an isomorphism, the
lisse-étale counterpart of `AlgebraicGeometry.Stack.isIso_of_flatObject`.

## Main results

* `AlgebraicGeometry.Stack.exists_isAffine_etale_covering_of_object`: an object of an algebraic
  stack has an étale covering family whose members lie over affine schemes and over étale
  morphisms of schemes; when the object is smooth, so are the members.
* `AlgebraicGeometry.Stack.affineSmoothFactorization_mem`: every object of `𝒳` is covered, for
  the fppf topology, by objects lying over affine schemes which have a morphism to a smooth
  object lying over an affine scheme.
* `AlgebraicGeometry.Stack.isIso_of_smoothObject`: a morphism of quasi-coherent modules which is
  bijective on the sections over every smooth object is an isomorphism.

## Implementation notes

The argument is the one of `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection`
with smooth objects in place of flat ones. Every object is covered by objects mapping to the
smooth object named by a smooth atlas (**Stacks 06XH**,
`AlgebraicGeometry.Stack.LisseEtale.hasLocalFactorizations_inclusion`); an affine open covering,
lifted cartesianly, refines both ends of such a morphism to objects lying over affine schemes, and
the lift of an open immersion into a smooth object is smooth
(`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`). Between objects lying over
affine schemes the sections of a quasi-coherent module are a base change (**Descent,
Proposition 03DX**), so bijectivity spreads from a smooth affine object to the affine objects
mapping to it (`AlgebraicGeometry.Stack.bijective_app_of_bijective_app`), and the sheaf property
gives bijectivity everywhere.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Étaleness of the underlying morphism of schemes of a morphism of the big fppf category over
`S` is unaffected by precomposition with the comparison isomorphism of an equality of objects. -/
private lemma etale_left_eqToHom_comp {V V' X : BigFppfOver B S hS} (h : V = V')
    (m : V' ⟶ X) (hm : Etale (B.inclusion.map m.left)) :
    Etale (B.inclusion.map (eqToHom h ≫ m).left) := by
  subst h
  simpa using hm

/-- **A scheme of the big fppf site is covered, for the étale topology, by affine schemes étale
over it.** An affine open covering, replaced by a tautologically equivalent chosen covering family
of the big site, is a chosen étale covering family. -/
theorem exists_isAffine_etale_ofArrows_mem_etaleTopology (T : B.Schemes) :
    ∃ W : PreZeroHypercover.{u + 1} T, Sieve.ofArrows W.X W.f ∈ etaleTopology B T ∧
      (∀ j, IsAffine (B.inclusion.obj (W.X j))) ∧ ∀ j, Etale (B.inclusion.map (W.f j)) := by
  let U := (B.inclusion.obj T).affineOpenCover.openCover
  obtain ⟨W, hW, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T U
  have hWet : ∀ j, Etale (B.inclusion.map (W.f j)) := fun j => by
    obtain ⟨e, he⟩ := hβ j
    have : AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (W.f j)) := by
      show AlgebraicGeometry.IsOpenImmersion ((W.map B.inclusion).f j)
      rw [← he]
      infer_instance
    infer_instance
  have hcov : IsEtaleCovering ⟨T, W⟩ := by
    show (W.map B.inclusion).presieve₀ ∈ Scheme.precoverage @Etale _
    refine (Scheme.presieve₀_mem_precoverage_iff (W.map B.inclusion)).2 ⟨fun z => ?_, hWet⟩
    obtain ⟨i, hi⟩ := U.exists_eq z
    obtain ⟨e, he⟩ := hα i
    obtain ⟨z, rfl⟩ := hi
    refine ⟨α i, e.hom.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, he]
  refine ⟨W, ?_, fun j => ?_, hWet⟩
  · have hpre : W.presieve₀ ∈ etalePrecoverage B T := ⟨W, rfl, hW, hcov⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  · obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := by
      show IsAffine (Spec ((B.inclusion.obj T).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance

/-- **An object of an algebraic stack is covered, for the étale topology, by objects lying over
affine schemes and over étale morphisms of schemes.** An affine open covering of the scheme `x`
lies over, replaced by a tautologically equivalent chosen covering family of the big site, is a
chosen étale covering family, and its cartesian lifts cover `x` (**Stacks 06NU**). -/
theorem exists_isAffine_etale_covering_of_object (x : 𝒳.val.val.obj) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳.val.val.obj) (f : ∀ i, y i ⟶ x),
      Sieve.generate (Presieve.ofArrows y f) ∈
        associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) x ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (y i)))) ∧
      ∀ i, Etale (B.inclusion.map (𝒳.val.val.p.map (f i)).left) := by
  classical
  have hfib := 𝒳.val.isFiberedInGroupoids.isFibered
  set X : BigFppfOver B S hS := 𝒳.val.val.p.obj x
  obtain ⟨W, hcov, hWaff, hWet⟩ := exists_isAffine_etale_ofArrows_mem_etaleTopology B X.left
  let Vobj (j : W.I₀) : BigFppfOver B S hS := Over.mk (W.f j ≫ X.hom)
  let vmap (j : W.I₀) : Vobj j ⟶ X := Over.homMk (W.f j)
  let y (j : W.I₀) : 𝒳.val.val.obj :=
    Functor.IsPreFibered.pullbackObj (p := 𝒳.val.val.p) (a := x) rfl (vmap j)
  let g (j : W.I₀) : y j ⟶ x :=
    Functor.IsPreFibered.pullbackMap (p := 𝒳.val.val.p) (a := x) rfl (vmap j)
  have hproj : ∀ j, 𝒳.val.val.p.obj (y j) = Vobj j := fun j =>
    Functor.IsPreFibered.pullbackObj_proj (p := 𝒳.val.val.p) (a := x) rfl (vmap j)
  have hfac : ∀ j, 𝒳.val.val.p.map (g j) = eqToHom (hproj j) ≫ vmap j := by
    intro j
    simpa using IsHomLift.fac' 𝒳.val.val.p (vmap j) (g j)
  refine ⟨W.I₀, y, g, ?_, fun j => (hproj j) ▸ hWaff j, fun j => ?_⟩
  · rw [associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.val.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows Vobj vmap ∈ (etaleTopology B).over (B.obj hS) X := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact hcov
    refine ((etaleTopology B).over (B.obj hS)).superset_covering ?_ hBcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    exact ⟨𝒳.val.val.p.obj (y j), eqToHom (hproj j).symm, 𝒳.val.val.p.map (g j),
      Presieve.ofArrows.mk j, by simp [hfac j]⟩
  · rw [hfac j]
    exact etale_left_eqToHom_comp B S hS (hproj j) (vmap j) (hWet j)

/-- The presieve on an object `y` of an algebraic stack of the morphisms whose source lies over
an affine scheme and admits a morphism to a smooth object lying over an affine scheme. -/
def affineSmoothFactorization (y : 𝒳.val.val.obj) : Presieve y := fun Y _ =>
  IsAffineOver B S hS (𝒳.val.val.p.obj Y) ∧
    ∃ x : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 x ∧
      IsAffineOver B S hS (𝒳.val.val.p.obj x) ∧ Nonempty (Y ⟶ x)

/-- **Every object of an algebraic stack is covered by affine objects mapping to smooth affine
objects.** A smooth atlas covers every object by objects mapping to a smooth object
(**Stacks 06XH**); the target is covered by smooth affine objects, lifting an affine open
covering of the scheme it lies over; and the source of the pulled back covering is covered by
affine objects in turn. -/
theorem affineSmoothFactorization_mem (y : 𝒳.val.val.obj) :
    Sieve.generate (affineSmoothFactorization B S hS 𝒳 y) ∈ fppfTopology B S hS 𝒳.val y := by
  refine GrothendieckTopology.transitive _
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale _
      (LisseEtale.hasLocalFactorizations_inclusion B S hS 𝒳 y)) _ ?_
  rintro Y h ⟨d, ⟨n⟩⟩
  obtain ⟨I, z, g, hcov, haff, het⟩ := exists_isAffine_etale_covering_of_object B S hS 𝒳 d.obj
  have hzsm : ∀ i, smoothObject.{u, w} B S hS 𝒳 (z i) := fun i =>
    LisseEtale.closedUnderSmoothMorphisms.{u, w} B S hS 𝒳 (g i) (by
      have := het i
      infer_instance) d.property
  refine GrothendieckTopology.transitive _
    (GrothendieckTopology.pullback_stable _ n
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale _ hcov)) _ ?_
  rintro Y' k ⟨Z, a, b, ⟨i⟩, hab⟩
  obtain ⟨I', w, e, hcov', haff', -⟩ := exists_isAffine_covering_of_object B S hS 𝒳.val Y'
  refine GrothendieckTopology.superset_covering _ ?_ hcov'
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨j⟩
  exact ⟨w j, 𝟙 _, e j ≫ k ≫ h, ⟨haff' j, z i, hzsm i, haff i, ⟨e j ≫ a⟩⟩, by simp⟩

section Modules

attribute [local instance] FibredSite.objModule

variable {B S hS 𝒳}

/-- A section of a sheaf of modules on an algebraic stack is determined by its restrictions to
the affine objects which map to smooth affine objects. -/
theorem sections_ext_of_affineSmoothFactorization
    {R : Sheaf (fppfTopology B S hS 𝒳.val) RingCat.{u}} (P : SheafOfModules.{u} R)
    {y : 𝒳.val.val.obj} {σ τ : P.val.obj (op y)}
    (h : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y), affineSmoothFactorization B S hS 𝒳 y f →
      P.val.map f.op σ = P.val.map f.op τ) : σ = τ := by
  refine (P.isSheaf_sections.isSheafFor _
    (affineSmoothFactorization_mem B S hS 𝒳 y)).isSeparatedFor.ext ?_
  rintro Y g ⟨Z, k, f, hf, rfl⟩
  show P.val.map (k ≫ f).op σ = P.val.map (k ≫ f).op τ
  rw [op_comp, P.val.map_comp_apply, P.val.map_comp_apply, h f hf]

/-- **A morphism of quasi-coherent modules on an algebraic stack which is bijective on the
sections over every smooth object is bijective on the sections over every object.** -/
theorem bijective_app_of_smoothObject
    {T P : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hT : T.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (ψ : T ⟶ P)
    (h : ∀ x : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 x →
      Function.Bijective (ψ.val.app (op x))) (y : 𝒳.val.val.obj) :
    Function.Bijective (ψ.val.app (op y)) := by
  have hloc : ∀ ⦃z Y : 𝒳.val.val.obj⦄ (f : Y ⟶ z), affineSmoothFactorization B S hS 𝒳 z f →
      Function.Bijective (ψ.val.app (op Y)) := by
    rintro z Y f ⟨hY, x, hx, hxa, ⟨n⟩⟩
    exact bijective_app_of_bijective_app hT hP ψ n hxa hY (h x hx)
  have hinj : ∀ z : 𝒳.val.val.obj, Function.Injective (ψ.val.app (op z)) := by
    intro z a b hab
    refine sections_ext_of_affineSmoothFactorization T (fun Y f hf => ?_)
    apply (hloc f hf).1
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hab]
  refine ⟨hinj y, fun s => ?_⟩
  let R := affineSmoothFactorization B S hS 𝒳 y
  have hsh : Presieve.IsSheafFor (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) R := by
    rw [Presieve.isSheafFor_iff_generate]
    exact T.isSheaf_sections.isSheafFor _ (affineSmoothFactorization_mem B S hS 𝒳 y)
  let pre : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y), R f → T.val.obj (op Y) := fun Y f hf =>
    (Equiv.ofBijective _ (hloc f hf)).symm (P.val.map f.op s)
  have ht : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y) (hf : R f),
      ψ.val.app (op Y) (pre f hf) = P.val.map f.op s := fun Y f hf =>
    (Equiv.ofBijective _ (hloc f hf)).apply_symm_apply _
  let t : Presieve.FamilyOfElements (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) R :=
    fun Y f hf => pre f hf
  have hcompat : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    apply hinj Z
    show ψ.val.app (op Z) (T.val.map g₁.op (pre f₁ hf₁)) =
      ψ.val.app (op Z) (T.val.map g₂.op (pre f₂ hf₂))
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, ht f₁ hf₁,
      ht f₂ hf₂, ← P.val.map_comp_apply, ← P.val.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  let a : T.val.obj (op y) := hsh.amalgamate t hcompat
  have ha : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y) (hf : R f), T.val.map f.op a = pre f hf :=
    fun Y f hf => hsh.valid_glue hcompat f hf
  refine ⟨a, sections_ext_of_affineSmoothFactorization P (fun Y f hf => ?_)⟩
  rw [← PresheafOfModules.naturality_apply, ha f hf, ht f hf]

/-- **A morphism of quasi-coherent modules on an algebraic stack which is bijective on the
sections over every smooth object is an isomorphism**: the smooth objects of an algebraic stack,
the objects of its lisse-étale site, see everything about its quasi-coherent modules. -/
theorem isIso_of_smoothObject
    {T P : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hT : T.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (ψ : T ⟶ P)
    (h : ∀ x : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 x →
      Function.Bijective (ψ.val.app (op x))) : IsIso ψ := by
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro y
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_app_of_smoothObject hT hP ψ h y.unop
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

end Modules

end AlgebraicGeometry.Stack

end
