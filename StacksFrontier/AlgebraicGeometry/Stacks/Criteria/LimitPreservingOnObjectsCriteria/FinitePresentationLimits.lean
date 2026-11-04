module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SheafFromSubsheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion

/-!
# Finite-presentation stages and sheaves of isomorphism classes

Auxiliary results for Stacks 07WH
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_limitPreservingOnObjects`).

An affine object of the big fppf site of `S` whose structure morphism factors through an affine
scheme locally of finite presentation over `S` is a cofiltered limit of affine objects locally of
finite presentation over `S` (Stacks 00QN), and a point of a category fibred in groupoids whose
structure morphism is limit preserving on objects descends along such a limit to a finite stage.
A functor into a category fibred in groupoids carrying a cartesian cone is identified with the
slice functor attached to a choice of pullbacks.

When the restriction to `Over V` of the first projection of a 2-fibre product is equivalent to
the category of a presheaf of sets, the fibres of that projection over `V` are thin, its sets of
isomorphism classes over `V` are small, and its restricted presheaf of isomorphism classes is
isomorphic to the given presheaf. A stack in setoids has a sheaf of isomorphism classes, and being
fibred in setoids and having small sets of isomorphism classes can be checked on a cover.

## Main results

* `AlgebraicGeometry.Stack.exists_isLimit_affine_locallyOfFinitePresentation`: such an affine
  object is a cofiltered limit of affine objects locally of finite presentation over `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

-- `Functor.Fiber`, `Functor.Fiber.fiberInclusion` and the slice functor attached to a choice of
-- pullbacks are plain `def`s, so an object of a fibre and its chosen pullbacks are only
-- recognised as such after unfolding them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.MorphismProperty.inverseImage

/-- Two morphisms into the domain of a strongly cartesian morphism which lie over one and the
same morphism of the base and agree after composition with it are equal. -/
private theorem eq_of_comp_isStronglyCartesian_eq {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮) {W W' W'' : 𝒮} {a b a' : 𝒳} {f : W ⟶ W'} {φ : a ⟶ b}
    (hφ : p.IsStronglyCartesian f φ) {g : W'' ⟶ W} {ψ ψ' : a' ⟶ a}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  Functor.IsStronglyCartesian.ext p f φ g h

/-- The image under a functor of a morphism conjugated by identifications of its source and
target. -/
private theorem map_eqToHom_conj {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {X Y X' Y' : C} (g : X ⟶ Y) (hX : X' = X) (hY : Y = Y') :
    R.map (eqToHom hX ≫ g ≫ eqToHom hY) =
      eqToHom (congrArg R.obj hX) ≫ R.map g ≫ eqToHom (congrArg R.obj hY) := by
  subst hX
  subst hY
  simp

/-- The factorisation of a morphism lying over a given morphism of the base, with the two
identifications of source and target supplied by the caller. -/
private theorem isHomLift_fac {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
    {W W' : 𝒮} {a b : 𝒳} (f : W ⟶ W') (φ : a ⟶ b) (h : p.IsHomLift f φ)
    (ha : p.obj a = W) (hb : W' = p.obj b) :
    p.map φ = eqToHom ha ≫ f ≫ eqToHom hb := by
  rw [IsHomLift.fac' p f φ]

/-- The composite of the structure morphism of an affine open restricted from a morphism with the
canonical map from the spectrum of its sections is the inclusion followed by that morphism. -/
private theorem resLE_isoSpec_hom_fromSpec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.affineOpens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V.1) :
    (f.resLE V.1 U e ≫ V.2.isoSpec.hom) ≫ V.2.fromSpec = U.ι ≫ f := by
  rw [Category.assoc, V.2.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι]

private lemma exists_finitePresentation_cocone
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : I ⥤ CommRingCat.{u}) (c : Limits.Cocone D)
      (s : (Functor.const I).obj (CommRingCat.of R) ⟶ D)
      (hcpt : c.pt = CommRingCat.of A), Nonempty (Limits.IsColimit c) ∧
      (∀ i, (s.app i).hom.FinitePresentation) ∧
      ∀ i, s.app i ≫ c.ι.app i = CommRingCat.ofHom (algebraMap R A) ≫
        eqToHom hcpt.symm := by
  classical
  obtain ⟨I, hI, hne, hdir, G, hG, hRG, f, hf, g, hg, hfp, _, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective R A
  let D : I ⥤ CommRingCat.{u} :=
    { obj := fun i => CommRingCat.of (G i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le).toRingHom
      map_id := by
        intro i
        ext x
        exact DirectedSystem.map_self (f := fun i j h => ⇑(f i j h)) x
      map_comp := by
        intro i j k h k'
        ext x
        exact (DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) h.le k'.le x).symm }
  let c : Limits.Cocone D :=
    { pt := CommRingCat.of A
      ι := { app := fun i => CommRingCat.ofHom (g i).toRingHom
             naturality := fun i j h => by ext x; exact hg i j (leOfHom h) x } }
  let s : (Functor.const I).obj (CommRingCat.of R) ⟶ D :=
    { app := fun i => CommRingCat.ofHom (algebraMap R (G i))
      naturality := fun i j h => by ext x; exact ((f i j (leOfHom h)).commutes x).symm }
  let c₀ : Limits.Cocone D :=
    { pt := CommRingCat.of (DirectLimit G f)
      ι := { app := fun i => CommRingCat.ofHom (DirectLimit.Algebra.of G f i).toRingHom
             naturality := fun i j h => by
               ext x
               exact DirectLimit.Algebra.of_f (leOfHom h) x } }
  have hc₀ : Limits.IsColimit c₀ :=
    { desc := fun t => CommRingCat.ofHom (DirectLimit.Ring.lift G f t.pt
        (fun i => (t.ι.app i).hom)
        (fun i j h x => congrArg (fun m : D.obj i ⟶ t.pt => m.hom x)
          (t.w (homOfLE h))))
      fac := fun t i => by ext x; rfl
      uniq := fun t m hm => by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using DirectLimit.induction with
        | _ i x => exact congrArg (fun m : D.obj i ⟶ t.pt => m.hom x) (hm i) }
  have hc : Limits.IsColimit c := hc₀.ofIsoColimit (Limits.Cocone.ext
    (RingEquiv.ofBijective (DirectLimit.Algebra.lift G f A g hg).toRingHom hbij).toCommRingCatIso
    (fun i => by ext x; rfl))
  refine ⟨I, hI, hne, hdir, D, c, s, rfl, ⟨hc⟩, ?_, ?_⟩
  · intro i
    change (algebraMap R (G i)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr (hfp i)
  · intro i
    ext x
    exact (g i).commutes x

private lemma exists_affine_finitePresentation_cone
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hR : B.Contains (Spec (CommRingCat.of R)))
    (hA : B.Contains (Spec (CommRingCat.of A)))
    (r : Spec (CommRingCat.of R) ⟶ S) [LocallyOfFinitePresentation r] :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS) (c : Limits.Cone D),
      c.pt = ⟨siteObject B S hS hA
        (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r),
          by change IsAffine (Spec (CommRingCat.of A)); infer_instance⟩ ∧
      Nonempty (Limits.IsLimit
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c)) ∧
      ∀ i, LocallyOfFinitePresentation
        (B.inclusion.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i)).hom) := by
  classical
  obtain ⟨I, hI, hne, hdir, D, ⟨P, ι⟩, s, hP, ⟨hc⟩, hfp, hcompat⟩ :=
    exists_finitePresentation_cocone R A
  dsimp only at hP
  subst P
  have hlfp (i : I) : LocallyOfFinitePresentation (Spec.map (s.app i)) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr (hfp i)
  have hsize (i : I) : B.Contains (Spec (D.obj i)) := by
    have := hlfp i
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (Spec.map (s.app i))
      hR
  let D' : Iᵒᵖ ⥤ AlgebraicGeometry.BigAffineFppf B S hS :=
    { obj := fun i => ⟨siteObject B S hS (hsize i.unop)
          (Spec.map (s.app i.unop) ≫ r),
          by change IsAffine (Spec (D.obj i.unop)); infer_instance⟩
      map := fun {i j} k => ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk (Spec.map (D.map k.unop))) (by
          apply B.inclusion.map_injective
          change Spec.map (D.map k.unop) ≫ (Spec.map (s.app j.unop) ≫ r) =
            Spec.map (s.app i.unop) ≫ r
          rw [← Category.assoc, ← Spec.map_comp]
          congr 2
          simpa using (s.naturality k.unop).symm))
      map_id := by
        intro i
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        simp [AlgebraicGeometry.siteObject, ObjectProperty.homMk,
          AlgebraicGeometry.BigFppfSite.obj]
      map_comp := by
        intro i j k a b
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        simp [AlgebraicGeometry.siteObject, ObjectProperty.homMk] }
  let c' : Limits.Cone D' :=
    { pt := ⟨siteObject B S hS hA
          (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r),
          by change IsAffine (Spec (CommRingCat.of A)); infer_instance⟩
      π :=
        { app := fun i => ObjectProperty.homMk (Over.homMk
            (ObjectProperty.homMk (Spec.map (ι.app i.unop))) (by
              apply B.inclusion.map_injective
              change Spec.map (ι.app i.unop) ≫ (Spec.map (s.app i.unop) ≫ r) = _
              rw [← Category.assoc, ← Spec.map_comp]
              simpa [AlgebraicGeometry.siteObject, ObjectProperty.homMk] using
                congrArg (fun q => Spec.map q ≫ r) (hcompat i.unop)))
          naturality := by
            intro i j k
            apply ObjectProperty.hom_ext
            apply Over.OverMorphism.ext
            apply ObjectProperty.hom_ext
            change Spec.map (ι.app j.unop) =
              Spec.map (ι.app i.unop) ≫ Spec.map (D.map k.unop)
            rw [← Spec.map_comp]
            congr 1
            simp } }
  refine ⟨Iᵒᵖ, inferInstance, inferInstance, D', c', rfl, ?_, ?_⟩
  · constructor
    change Limits.IsLimit (Scheme.Spec.mapCone
      (⟨CommRingCat.of A, ι⟩ : Limits.Cocone D).op)
    exact Limits.isLimitOfPreserves Scheme.Spec hc.op
  · intro i
    have := hlfp i.unop
    change LocallyOfFinitePresentation (Spec.map (s.app i.unop) ≫ r)
    infer_instance

/-- An affine object of the big fppf site over `S` whose structure morphism factors through
`r : Spec R ⟶ S` is isomorphic to the object attached to an `R`-algebra `A`. -/
private lemma exists_algebra_siteObject_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine U.left.1]
    (R : CommRingCat.{u}) (r : Spec R ⟶ S)
    (q : U.left.1 ⟶ Spec R) (hq : q ≫ r = B.inclusion.map U.hom) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (hA : B.Contains (Spec (CommRingCat.of A))),
      Nonempty (siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r) ≅ U) := by
  classical
  let A := U.left.1.presheaf.obj (Opposite.op ⊤)
  let a : R ⟶ A := (Scheme.Spec.preimage (U.left.1.isoSpec.inv ≫ q)).unop
  let : Algebra R A := a.hom.toAlgebra
  have hA : B.Contains (Spec A) := by
    change (Spec A).size < B.cutoff
    rw [← Scheme.size_congr U.left.1.isoSpec]
    exact U.left.2
  have ha : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r =
      U.left.1.isoSpec.inv ≫ B.inclusion.map U.hom := by
    change Spec.map a ≫ r = _
    have ha' : Spec.map a = U.left.1.isoSpec.inv ≫ q := Scheme.Spec.map_preimage _
    rw [ha', Category.assoc, hq]
  exact ⟨A, inferInstance, inferInstance, hA, ⟨Over.isoMk
    (ObjectProperty.isoMk _ U.left.1.isoSpec.symm) (B.inclusion.map_injective ha.symm)⟩⟩

/-- **An affine object of the big fppf site of `S` over an affine scheme locally of finite
presentation over `S` is a cofiltered limit of affine objects locally of finite presentation
over `S`.** Let `U` be an object of the site with affine underlying scheme whose structure
morphism factors through `r : Spec R ⟶ S`, locally of finite presentation. Then there is a
cofiltered diagram of affine objects of the site, each locally of finite presentation over
`S`, and a cone on it with vertex isomorphic to `U` which is a limit cone after passing to
schemes.

Writing `U = Spec A`, the diagram is that of the spectra of a directed system of finitely
presented `R`-algebras with colimit `A`. -/
theorem exists_isLimit_affine_locallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine U.left.1]
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R))
    (r : Spec R ⟶ S) [LocallyOfFinitePresentation r]
    (q : U.left.1 ⟶ Spec R) (hq : q ≫ r = B.inclusion.map U.hom) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS)
      (c : Limits.Cone (D ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS))
      (_ : c.pt ≅ U),
      Nonempty (Limits.IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c)) ∧
      ∀ i, LocallyOfFinitePresentation
        (B.inclusion.map
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i)).hom) := by
  classical
  obtain ⟨A, _, _, hA, ⟨e⟩⟩ := exists_algebra_siteObject_iso B S hS U R r q hq
  obtain ⟨I, hI, hco, D, ⟨W, π⟩, hW, ⟨hc⟩, hfp⟩ :=
    exists_affine_finitePresentation_cone B S hS R A hR hA r
  dsimp only at hW
  subst W
  exact ⟨I, hI, hco, D, (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).mapCone ⟨_, π⟩, e,
    ⟨hc⟩, hfp⟩

private lemma exists_stage_of_isLimitPreservingOnObjects
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒴
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒴)))
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS) (c : Limits.Cone D)
    (hc : Limits.IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c))
    (x : 𝒴.val.p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt)) :
    ∃ (i : I)
      (x' : 𝒴.val.p.Fiber
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (φ : x.1 ⟶ x'.1),
      𝒴.val.p.IsStronglyCartesian
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)) φ := by
  classical
  let i : I := Classical.choice (IsCofiltered.nonempty (C := I))
  let J := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let γ : 𝒴.val.p.obj x.1 ⟶ J.obj (D.obj i) :=
    eqToHom x.2 ≫ J.map (c.π.app i)
  have hγ : (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)).IsHomLift
      (J.map (c.π.app i)) γ := by
    apply IsHomLift.of_fac (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) _ _ x.2 rfl
    simp [γ]
  have hγc : (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)).IsStronglyCartesian
      (J.map (c.π.app i)) γ :=
    Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  obtain ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcompat⟩ :=
    hlimit I D c hc i ⟨J.obj (D.obj i), rfl⟩ x γ hγc
  have : 𝒴.val.p.IsHomLift (𝟙 (J.obj c.pt)) β := hβ
  have : 𝒴.val.p.IsHomLift (J.map (c.π.app i')) δ := hδ.toIsHomLift
  have hβinv : 𝒴.val.p.IsHomLift (𝟙 (J.obj c.pt)) (inv β) :=
    IsHomLift.lift_id_inv_isIso 𝒴.val.p _ β
  refine ⟨i', x', inv β ≫ δ, ?_⟩
  have : 𝒴.val.p.IsHomLift (J.map (c.π.app i')) (inv β ≫ δ) := by
    simpa only [Category.id_comp] using
      IsHomLift.comp 𝒴.val.p (𝟙 (J.obj c.pt)) (J.map (c.π.app i')) (inv β) δ
  exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

private lemma exists_finitePresentation_stage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒴
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒴)))
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hR : B.Contains (Spec (CommRingCat.of R)))
    (hA : B.Contains (Spec (CommRingCat.of A)))
    (r : Spec (CommRingCat.of R) ⟶ S) [LocallyOfFinitePresentation r]
    (x : 𝒴.val.p.Fiber (siteObject B S hS hA
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r))) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS), IsAffine U.left.1 ∧
      LocallyOfFinitePresentation (B.inclusion.map U.hom) ∧
      ∃ (g : siteObject B S hS hA
          (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r) ⟶ U)
        (x' : 𝒴.val.p.Fiber U) (φ : x.1 ⟶ x'.1),
        𝒴.val.p.IsStronglyCartesian g φ := by
  obtain ⟨I, hI, hco, D, ⟨W, π⟩, hW, ⟨hc⟩, hfp⟩ :=
    exists_affine_finitePresentation_cone B S hS R A hR hA r
  dsimp only at hW
  subst W
  obtain ⟨i, x', φ, hφ⟩ := exists_stage_of_isLimitPreservingOnObjects
    B S hS 𝒴 hlimit I D ⟨_, π⟩ hc x
  exact ⟨(D.obj i).obj, (D.obj i).property, hfp i,
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (π.app i), x', φ, hφ⟩

private lemma exists_finitePresentation_stage_of_isAffine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒴
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒴)))
    (U : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine U.left.1]
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R))
    (r : Spec R ⟶ S) [LocallyOfFinitePresentation r]
    (q : U.left.1 ⟶ Spec R) (hq : q ≫ r = B.inclusion.map U.hom)
    (x : 𝒴.val.p.Fiber U) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS), IsAffine V.left.1 ∧
      LocallyOfFinitePresentation (B.inclusion.map V.hom) ∧
      ∃ (g : U ⟶ V) (x' : 𝒴.val.p.Fiber V) (φ : x.1 ⟶ x'.1),
        𝒴.val.p.IsStronglyCartesian g φ := by
  classical
  obtain ⟨A, _, _, hA, ⟨e⟩⟩ := exists_algebra_siteObject_iso B S hS U R r q hq
  obtain ⟨xA, ψ, hψ⟩ := 𝒴.2.exists_lift e.hom x.1 x.2
  have : 𝒴.val.p.IsHomLift e.hom ψ := hψ
  have : 𝒴.val.p.IsStronglyCartesian e.hom ψ :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have : IsIso ψ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.p e.hom ψ
  let xA' : 𝒴.val.p.Fiber (siteObject B S hS hA
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ r)) :=
    ⟨xA, IsHomLift.domain_eq 𝒴.val.p e.hom ψ⟩
  obtain ⟨V, hV, hVfp, g, x', φ, hφ⟩ :=
    exists_finitePresentation_stage B S hS 𝒴 hlimit R A hR hA r xA'
  have : 𝒴.val.p.IsHomLift g φ := hφ.toIsHomLift
  have : 𝒴.val.p.IsHomLift e.inv (inv ψ) := by
    simpa using IsHomLift.inv 𝒴.val.p e.hom ψ
  refine ⟨V, hV, hVfp, e.inv ≫ g, x', inv ψ ≫ φ, ?_⟩
  have : 𝒴.val.p.IsHomLift (e.inv ≫ g) (inv ψ ≫ φ) :=
    IsHomLift.comp 𝒴.val.p e.inv g (inv ψ) φ
  exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

private lemma exists_iso_sliceFunctor_of_cartesian_cone
    {C D Y : Type*} [Category C] [Category D] [Category Y]
    (p : Y ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {V : C} (x : p.Fiber V)
    (k : D ⥤ Over V) (y : D ⥤ Y)
    (hy : y ⋙ p = k ⋙ Over.forget V)
    (τ : y ⟶ (Functor.const D).obj x.1)
    (hτ : ∀ d, p.IsHomLift (k.obj d).hom (τ.app d)) :
    ∃ e : y ≅ k ⋙ c.sliceFunctor x,
      ∀ d, p.IsHomLift (𝟙 (k.obj d).left) (e.hom.app d) := by
  classical
  let := c.isFibered
  let (d : D) : p.IsHomLift (k.obj d).hom (τ.app d) := hτ d
  let (d : D) : p.IsStronglyCartesian (k.obj d).hom (τ.app d) :=
    hp.isStronglyCartesian_homLift _ _
  let e (d : D) : y.obj d ≅ (c.sliceFunctor x).obj (k.obj d) :=
    Functor.IsCartesian.domainUniqueUpToIso p (k.obj d).hom
      (c.map (k.obj d).hom x) (τ.app d)
  have he (d : D) : p.IsHomLift (𝟙 (k.obj d).left) (e d).hom := by
    dsimp [e]
    infer_instance
  have hfac (d : D) : (e d).hom ≫ c.map (k.obj d).hom x = τ.app d := by
    have : p.IsHomLift (k.obj d).hom (τ.app d) := hτ d
    exact Functor.IsCartesian.fac p (k.obj d).hom
      (c.map (k.obj d).hom x) (τ.app d)
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro d d' a
  have hya : p.IsHomLift (k.map a).left (y.map a) := by
    have hk : (k ⋙ Over.forget V).IsHomLift (k.map a).left a := by
      simpa only [Functor.comp_map, Over.forget_map] using
        (IsHomLift.map (k ⋙ Over.forget V) a)
    exact Functor.isHomLift_map_of_comp_eq hy (k.map a).left a
  let := he d
  let := he d'
  have h₁ : p.IsHomLift (k.map a).left (y.map a ≫ (e d').hom) :=
    IsHomLift.comp_lift_id_right p _ _ _
  have hmap : p.IsHomLift (k.map a).left ((c.sliceFunctor x).map (k.map a)) :=
    c.sliceFunctor_map_isHomLift x (k.map a)
  have h₂ : p.IsHomLift (k.map a).left
      ((e d).hom ≫ (k ⋙ c.sliceFunctor x).map a) := by
    change p.IsHomLift (k.map a).left
      ((e d).hom ≫ (c.sliceFunctor x).map (k.map a))
    exact IsHomLift.comp_lift_id_left p _ _ _
  refine eq_of_comp_isStronglyCartesian_eq p (c.isStronglyCartesian (k.obj d').hom x) h₁ h₂ ?_
  calc (y.map a ≫ (e d').hom) ≫ c.map (k.obj d').hom x
      = y.map a ≫ (e d').hom ≫ c.map (k.obj d').hom x := Category.assoc _ _ _
    _ = y.map a ≫ τ.app d' := congrArg (fun m => y.map a ≫ m) (hfac d')
    _ = τ.app d ≫ ((Functor.const D).obj x.1).map a := τ.naturality a
    _ = τ.app d := Category.comp_id _
    _ = (e d).hom ≫ c.map (k.obj d).hom x := (hfac d).symm
    _ = (e d).hom ≫ (c.sliceFunctor x).map (k.map a) ≫ c.map (k.obj d').hom x :=
        congrArg (fun m => (e d).hom ≫ m) (c.sliceFunctor_map_fac x (k.map a)).symm
    _ = ((e d).hom ≫ (k ⋙ c.sliceFunctor x).map a) ≫ c.map (k.obj d').hom x :=
        (Category.assoc _ _ _).symm

private lemma exists_iso_iteratedSliceFunctor_of_cartesian
    {C Y : Type*} [Category C] [Category Y]
    {S : C} (p : Y ⥤ Over S) (hp : p.IsFiberedInGroupoids)
    (c : p.ChoiceOfPullbacks) {U V : Over S} (g : U ⟶ V)
    (x' : p.Fiber V)
    (y : Over U.left ⥤ Y) (hy : y ⋙ p = Over.map U.hom)
    (φ : y.obj (Over.mk (𝟙 U.left)) ⟶ x'.1)
    (hφ : p.IsStronglyCartesian g φ)
    :
    ∃ e : y ≅ (U.iteratedSliceBackward ⋙ Over.map g) ⋙ c.sliceFunctor x',
      ∀ W, p.IsHomLift (𝟙 ((U.iteratedSliceBackward ⋙ Over.map g).obj W).left)
        (e.hom.app W) := by
  classical
  let t : Over U.left := Over.mk (𝟙 U.left)
  let toTerminal (W : Over U.left) : W ⟶ t :=
    Over.homMk W.hom (by simp [t])
  let τ : y ⟶ (Functor.const (Over U.left)).obj x'.1 :=
    { app := fun W => y.map (toTerminal W) ≫ φ
      naturality := by
        intro W W' a
        have hcomp : a ≫ toTerminal W' = toTerminal W := by
          apply Over.OverMorphism.ext
          simp [toTerminal]
        dsimp
        simpa only [Category.comp_id] using
          (show y.map a ≫ (y.map (toTerminal W') ≫ φ) =
              y.map (toTerminal W) ≫ φ by
            rw [← Category.assoc, ← y.map_comp, hcomp]) }
  have hτ (W : Over U.left) : p.IsHomLift
      ((U.iteratedSliceBackward ⋙ Over.map g).obj W).hom (τ.app W) := by
    have hmap : p.IsHomLift
        (U.iteratedSliceBackward.obj W).hom (y.map (toTerminal W)) := by
      have hW := Functor.congr_obj hy W
      have ht := Functor.congr_obj hy t
      have hmk : Over.mk U.hom = U := by cases U; rfl
      change p.obj (y.obj t) = Over.mk (𝟙 U.left ≫ U.hom) at ht
      have hdom : p.obj (y.obj W) = (U.iteratedSliceBackward.obj W).left := by
        calc
          p.obj (y.obj W) = (Over.map U.hom).obj W := by
            simpa only [Functor.comp_obj] using hW
          _ = (U.iteratedSliceBackward.obj W).left := by
            simp [Over.iteratedSliceBackward, Over.map, Comma.mapRight]
            cases W
            rfl
      have hcod : p.obj (y.obj t) = U := by
        simpa only [Category.id_comp, hmk] using ht
      have hfac : p.map (y.map (toTerminal W)) =
          eqToHom hdom ≫ (U.iteratedSliceBackward.obj W).hom ≫ eqToHom hcod.symm := by
        change (y ⋙ p).map (toTerminal W) = _
        rw [Functor.congr_hom hy (toTerminal W)]
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.eqToHom_left]
        simp [toTerminal, Over.iteratedSliceBackward]
      exact IsHomLift.of_fac' p _ _ hdom hcod hfac
    have : p.IsHomLift g φ := hφ.toIsHomLift
    convert IsHomLift.comp p (U.iteratedSliceBackward.obj W).hom g
      (y.map (toTerminal W)) φ using 1 <;> try rfl
  have hk : ((U.iteratedSliceBackward ⋙ Over.map g) ⋙ Over.forget V) =
      Over.map U.hom := by
    rw [Functor.assoc, Over.mapForget_eq]
    exact Over.iteratedSliceBackward_forget U
  exact exists_iso_sliceFunctor_of_cartesian_cone p hp c x'
    (U.iteratedSliceBackward ⋙ Over.map g) y (by rw [hk, hy]) τ hτ

section BaseChange

open CategoryTheory.Functor

universe uC vC uT vT uD vD uA vA uY vY
variable {C : Type uC} [Category.{vC} C] {T : Type uT} [Category.{vT} T]
  {D : Type uD} [Category.{vD} D] {A : Type uA} [Category.{vA} A]
  {Y : Type uY} [Category.{vY} Y]

private theorem baseChange_fiber_isThin
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y)
    (hq : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInSetoids)
    (V : D) :
    Quiver.IsThin
      ((TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).Fiber V) := by
  let p := TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F
  let Φ := AlgebraicGeometry.baseChangeFiberFunctor R pT pA pY G F V
  intro P Q
  constructor
  intro φ ψ
  have he : Φ.map φ = Φ.map ψ :=
    (hq.fiber_isThin (R.obj V) _ _).allEq _ _
  apply Subtype.ext
  apply TwoFibreProductOver.Hom.ext'
  · have : p.IsHomLift (𝟙 V) φ.1 := φ.2
    have : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
    exact (IsHomLift.fac' p (𝟙 V) φ.1).trans
      (IsHomLift.fac' p (𝟙 V) ψ.1).symm
  · exact congrArg (fun a => a.1.b) he

private theorem fiber_isThin_of_baseChange
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (V : D)
    (ht : Quiver.IsThin
      ((TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).Fiber V)) :
    Quiver.IsThin ((TwoFibreProductOver.fst pT pA pY G F).Fiber (R.obj V)) := by
  let Φ := AlgebraicGeometry.baseChangeFiberFunctor R pT pA pY G F V
  have : Φ.Full := AlgebraicGeometry.baseChangeFiberFunctor_full R pT pA pY G F V
  intro P Q
  obtain ⟨P, rfl⟩ := AlgebraicGeometry.baseChangeFiberFunctor_obj_surjective R pT pA pY G F V P
  obtain ⟨Q, rfl⟩ := AlgebraicGeometry.baseChangeFiberFunctor_obj_surjective R pT pA pY G F V Q
  constructor
  intro a b
  calc
    a = Φ.map (Φ.preimage a) := (Φ.map_preimage a).symm
    _ = Φ.map (Φ.preimage b) := congrArg Φ.map ((ht P Q).allEq _ _)
    _ = b := Φ.map_preimage b

private theorem baseChange_isFiberedInSetoids
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y)
    (hp : (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).IsFiberedInGroupoids)
    (hq : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInSetoids) :
    (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).IsFiberedInSetoids :=
  ⟨hp, baseChange_fiber_isThin R pT pA pY G F hq⟩

private theorem baseChange_isFiberedInSetoidsOfCompEq
    (R : D ⥤ T) (pD : D ⥤ C) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (hR : R ⋙ pT = pD)
    (hp : (TwoFibreProductOver.fst pD pA pY (R ⋙ G) F).IsFiberedInGroupoids)
    (hq : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInSetoids) :
    (TwoFibreProductOver.fst pD pA pY (R ⋙ G) F).IsFiberedInSetoids := by
  subst pD
  exact baseChange_isFiberedInSetoids R pT pA pY G F hp hq

private lemma fst_fiber_isThin_of_represented_restriction
    {C : Type (u + 1)} [Category.{u} C]
    {A Y : Type (u + 1)} [Category.{u} A] [Category.{u} Y]
    {V U S : C} (g : V ⟶ U) (a : U ⟶ S)
    (pA : A ⥤ Over S) (pY : Y ⥤ Over S) (G : Over U ⥤ Y) (F : A ⥤ Y)
    (P : (Over V)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (g ≫ a)) pA pY (Over.map g ⋙ G) F)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    Quiver.IsThin ((TwoFibreProductOver.fst (Over.map a) pA pY G F).Fiber
      (Over.mk g)) := by
  have hs := StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver e
    (PresheafOfCategories.isFiberedInSetoids_discreteProjection P)
  have ht := hs.fiber_isThin (Over.mk (𝟙 V))
  have ht' : Quiver.IsThin
      ((TwoFibreProductOver.fst (Over.map g ⋙ Over.map a) pA pY (Over.map g ⋙ G) F).Fiber
        (Over.mk (𝟙 V))) := by
    rwa [Over.mapComp_eq g a] at ht
  have H := fiber_isThin_of_baseChange (Over.map g) (Over.map a) pA pY G F
    (Over.mk (𝟙 V)) ht'
  change Quiver.IsThin ((TwoFibreProductOver.fst (Over.map a) pA pY G F).Fiber
    (Over.mk (𝟙 V ≫ g))) at H
  rwa [Category.id_comp] at H

private lemma small_fst_isoClass_of_represented_restriction
    {C : Type (u + 1)} [Category.{u} C]
    {A Y : Type (u + 1)} [Category.{u} A] [Category.{u} Y]
    {V U S : C} (g : V ⟶ U) (a : U ⟶ S)
    (pA : A ⥤ Over S) (pY : Y ⥤ Over S) (G : Over U ⥤ Y) (F : A ⥤ Y)
    (hq : (TwoFibreProductOver.fst (Over.map a) pA pY G F).IsFiberedInGroupoids)
    (P : (Over V)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (g ≫ a)) pA pY (Over.map g ⋙ G) F)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    letI := hq.isFibered
    Small.{u} ((TwoFibreProductOver.fst (Over.map a) pA pY G F).isoClassPresheaf.obj
      (.op (Over.mk g))) := by
  let := hq.isFibered
  have hp := (StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver e
    (PresheafOfCategories.isFiberedInSetoids_discreteProjection P)).isFiberedInGroupoids
  let := hp.isFibered
  let i := AlgebraicGeometry.baseChangeIsoClassPresheafIsoOfCompEq
    (Over.map g) (Over.map (g ≫ a)) (Over.map a) pA pY G F
    (Over.mapComp_eq g a).symm hp hq
  let e' := (i.app (.op (Over.mk (𝟙 V)))).toEquiv.symm.trans
    (PresheafOfCategories.elementsIsoClassEquiv P e (Over.mk (𝟙 V)))
  have H : Small.{u}
      (((Over.map g).op ⋙
        (TwoFibreProductOver.fst (Over.map a) pA pY G F).isoClassPresheaf).obj
          (.op (Over.mk (𝟙 V)))) := small_map e'
  change Small.{u} ((TwoFibreProductOver.fst (Over.map a) pA pY G F).isoClassPresheaf.obj
    (.op (Over.mk (𝟙 V ≫ g)))) at H
  rwa [Category.id_comp] at H

private noncomputable def representedRestrictionIso
    {C : Type (u + 1)} [Category.{u} C]
    {A Y : Type (u + 1)} [Category.{u} A] [Category.{u} Y]
    {V U S : C} (g : V ⟶ U) (a : U ⟶ S)
    (pA : A ⥤ Over S) (pY : Y ⥤ Over S) (G : Over U ⥤ Y) (F : A ⥤ Y)
    (hq : (TwoFibreProductOver.fst (Over.map a) pA pY G F).IsFiberedInGroupoids)
    (P : (Over V)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (g ≫ a)) pA pY (Over.map g ⋙ G) F)
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (Z : (Over U)ᵒᵖ ⥤ Type u)
    (eZ : letI := hq.isFibered
      ∀ W, (TwoFibreProductOver.fst (Over.map a) pA pY G F).isoClassPresheaf.obj W ≃
        Z.obj W)
    (heZ : letI := hq.isFibered
      ∀ ⦃W W'⦄ (k : W ⟶ W') (x),
        eZ W' ((TwoFibreProductOver.fst (Over.map a) pA pY G F).isoClassPresheaf.map k x) =
          Z.map k (eZ W x)) :
    P ≅ (Over.map g).op ⋙ Z := by
  letI := hq.isFibered
  have hp := (StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver e
    (PresheafOfCategories.isFiberedInSetoids_discreteProjection P)).isFiberedInGroupoids
  letI := hp.isFibered
  let i := AlgebraicGeometry.baseChangeIsoClassPresheafIsoOfCompEq
    (Over.map g) (Over.map (g ≫ a)) (Over.map a) pA pY G F
    (Over.mapComp_eq g a).symm hp hq
  let ε (W : (Over V)ᵒᵖ) := PresheafOfCategories.elementsIsoClassEquiv P e W.unop
  refine NatIso.ofComponents (fun W =>
    ((ε W).symm.trans ((i.app W).toEquiv.trans (eZ ((Over.map g).op.obj W)))).toIso) ?_
  intro W W' k
  ext x
  have hε : (ε W').symm (P.map k x) =
      (TwoFibreProductOver.fst (Over.map (g ≫ a)) pA pY (Over.map g ⋙ G) F).isoClassPresheaf.map
        k ((ε W).symm x) := by
    apply (ε W').injective
    simp only [Equiv.apply_symm_apply]
    simpa only [ε, Equiv.apply_symm_apply, Quiver.Hom.op_unop] using
      (PresheafOfCategories.elementsIsoClassEquiv_naturality hp P e k.unop
        ((ε W).symm x)).symm
  change eZ _ (i.hom.app W' ((ε W').symm (P.map k x))) =
    Z.map ((Over.map g).op.map k) (eZ _ (i.hom.app W ((ε W).symm x)))
  rw [hε, NatTrans.naturality_apply]
  exact heZ _ _

end BaseChange

section IsoClassSheaf

open CategoryTheory.Functor Opposite
universe uC vC uD vD

private lemma isSheaf_isoClassPresheaf
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (p : D ⥤ C) [hp : p.IsFiberedInSetoids]
    (J : GrothendieckTopology C) (h : p.IsStack J) :
    Presheaf.IsSheaf J p.isoClassPresheaf := by
  classical
  have thin (V : C) : Quiver.IsThin (p.Fiber V) := hp.fiber_isThin V
  have grp (V : C) : IsGroupoid (p.Fiber V) := hp.isFiberedInGroupoids.fiber_isGroupoid V
  rw [isSheaf_iff_isSheaf_of_type]
  intro V R hR fam hfam
  let d : SieveDescentDatum p R :=
    { obj := fun {W} f hf => Quotient.out (fam f hf)
      iso := fun {_ _ _} {_} hf {_} hg ε ε' heq => (exists_iso_of_isoClassMk_eq (by
        rw [← isoClassPresheaf_map_isoClassMk, ← isoClassPresheaf_map_isoClassMk]
        simpa only [isoClassMk, Quotient.out_eq] using hfam ε ε' hf hg heq)).some
      cocycle := by intros; exact Subsingleton.elim _ _
      iso_pullback := by intros; exact Subsingleton.elim _ _ }
  obtain ⟨x, ζ, hζ, _⟩ := h.hasEffectiveDescent R hR d
  have hx : fam.IsAmalgamation (isoClassMk p x) := by
    intro W f hf
    rw [isoClassPresheaf_map_isoClassMk]
    have hc := hζ f hf
    exact (isoClassMk_eq_pullbackFiber_of_isCartesian f x (d.obj f hf)
      (ζ f hf) hc.toIsHomLift hc).symm.trans (Quotient.out_eq _)
  refine ⟨isoClassMk p x, hx, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := isoClassMk_surjective z
  have hlocal {W : C} (f : W ⟶ V) (hf : R f) :
      Nonempty (pullbackFiber p a f ≅ pullbackFiber p x f) := by
    apply exists_iso_of_isoClassMk_eq
    simpa only [← isoClassPresheaf_map_isoClassMk] using (hz f hf).trans (hx f hf).symm
  let R' := (Sieve.overEquiv (Over.mk (𝟙 V))).symm R
  let m : Presieve.FamilyOfElements (morPresheaf p a x) (R' : Presieve (Over.mk (𝟙 V))) :=
    fun {Z} k hk => by
      have hZ : Z.hom = k.left := by simpa using k.w.symm
      exact ((hZ ▸ hlocal k.left hk).some).hom
  obtain ⟨t, _⟩ := (isSheaf_iff_isSheaf_of_type _ _).1 (h.isMorSheaf V a x) R'
    (J.overEquiv_symm_mem_over (Over.mk (𝟙 V)) R hR) m
    (by intro Z Z' W a b f g hf hg hab; exact (thin W.left _ _).allEq _ _)
  exact isoClassMk_eq_of_iso ((pullbackFiberIdIso a).symm ≪≫
    asIso t ≪≫ pullbackFiberIdIso x)

private lemma isFiberedInSetoids_of_locally_isThin
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids)
    (J : GrothendieckTopology C) (h : p.IsStack J)
    (hloc : ∀ U : C, ∃ R : Sieve U, R ∈ J U ∧
      ∀ ⦃V⦄ (f : V ⟶ U), R f → Quiver.IsThin (p.Fiber V)) :
    p.IsFiberedInSetoids := by
  let := hp.isFibered
  refine ⟨hp, fun U x y => ⟨fun a b => ?_⟩⟩
  obtain ⟨R, hR, hthin⟩ := hloc U
  exact eq_of_pullbackFiberHom_locally_eq p (h.isMorSheaf U x y) hR
    (fun {_} f hf => (hthin f hf _ _).allEq _ _)

private lemma isFiberedInSetoids_of_thin_cover
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids)
    (J : GrothendieckTopology C) (h : p.IsStack J)
    (hloc : ∀ U : C, ∃ (I : Type vD) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, Quiver.IsThin (p.Fiber (V i))) :
    p.IsFiberedInSetoids := by
  let := hp.isFibered
  refine ⟨hp, fun U x y => ⟨fun a b => ?_⟩⟩
  obtain ⟨I, V, f, hcover, hthin⟩ := hloc U
  let V' : I → Over U := fun i => Over.mk (f i)
  let f' : ∀ i, V' i ⟶ Over.mk (𝟙 U) :=
    fun i => Over.homMk (f i) (by change f i ≫ 𝟙 U = f i; simp)
  have hcover' : Sieve.ofArrows V' f' ∈ J.over U (Over.mk (𝟙 U)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hcover
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp
    (h.isMorSheaf U x y) _ hcover').isSeparatedFor
  have hsep' := Presieve.isSeparatedFor_iff_generate.mpr hsep
  apply morSection_injective p x y
  apply hsep'.ext
  rintro Z g ⟨i⟩
  exact (hthin i _ _).allEq _ _

private lemma small_obj_of_isSheaf_cover
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type uD) (hF : Presheaf.IsSheaf J F) {U : C}
    {I : Type vD} (V : I → C) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    [∀ i, Small.{vD} (F.obj (op (V i)))] : Small.{vD} (F.obj (op U)) := by
  apply small_of_injective (f := fun x i => F.map (f i).op x)
  intro x y hxy
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp hF _ hf).isSeparatedFor
  have hsep' : Presieve.IsSeparatedFor F (Presieve.ofArrows V f) :=
    Presieve.isSeparatedFor_iff_generate.mpr hsep
  apply hsep'.ext
  rintro W a ⟨i⟩
  exact congrFun hxy _

end IsoClassSheaf

end AlgebraicGeometry.Stack

end
