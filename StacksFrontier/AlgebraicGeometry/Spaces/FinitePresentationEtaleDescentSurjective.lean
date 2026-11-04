module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberPerMemberIsoDirect
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleHomRestrictionTwoSided
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Descent of finitely presented modules along a surjective étale morphism

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces which is surjective on points.  A
finitely presented module on `Y` with an isomorphism of its two inverse images to `Y ×_X Y`
satisfying the cocycle condition is the inverse image of a finitely presented module on `X`.
Finite presentation of the descended module is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_etaleModulePullback` of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSurjectiveEtaleDescent`.

## Main results

* `AlgebraicGeometry.Space.exists_descent_of_isEtale`: **descent of finitely presented modules
  along a surjective étale morphism**: a finitely presented module on `Y` with an isomorphism of
  its two inverse images to `Y ×_X Y` satisfying the cocycle condition is the inverse image of a
  finitely presented module on `X`, compatibly with the isomorphism.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

open QuasiCoherentDescent in
/-- A pairwise isomorphism read on a test space is its two-sided restriction. -/
theorem transitionOn_hom {I : Type*} (Yi : I → AlgebraicSpaces B S hS) (f : ∀ i, Yi i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Yi i).1 (Yi i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Yi f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Yi f i j)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (hi : v ≫ pairFst B S hS Yi f i j = vi)
    (hj : v ≫ pairSnd B S hS Yi f i j = vj) :
    (transitionOn B S hS Yi f F φ i j v vi vj hi hj).hom =
      moduleHomRestrict₂ (F i) (F j) v _ _ vi vj hi hj (φ i j).hom := rfl

open QuasiCoherentDescent in
/-- For a single morphism `g : Y ⟶ X` and an isomorphism `φ` of the two inverse images of `F` to
`Y ×_X Y`, the transition isomorphisms read on a test space satisfy the cocycle condition whenever
the two-sided restrictions of `φ` do. -/
theorem transitionOn_unit_trans (g : Y ⟶ X) {F : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F ≅
      (modulePullback B S hS (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F)
    (T : AlgebraicSpaces B S hS) (vi vj vk : T ⟶ Y)
    (vij vjk vik : T ⟶ pair B S hS (fun _ : Unit => Y) (fun _ => g) () ())
    (hij₀ : vij ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
    (hij₁ : vij ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
    (hjk₀ : vjk ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk)
    (hik₀ : vik ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
    (hik₁ : vik ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk)
    (h : moduleHomRestrict₂ F F vij _ _ vi vj hij₀ hij₁ φ.hom ≫
          moduleHomRestrict₂ F F vjk _ _ vj vk hjk₀ hjk₁ φ.hom =
        moduleHomRestrict₂ F F vik _ _ vi vk hik₀ hik₁ φ.hom) :
    transitionOn B S hS (fun _ : Unit => Y) (fun _ => g) (fun _ => F) (fun _ _ => φ) () () vij vi
        vj hij₀ hij₁ ≪≫
      transitionOn B S hS (fun _ : Unit => Y) (fun _ => g) (fun _ => F) (fun _ _ => φ) () () vjk vj
        vk hjk₀ hjk₁ =
      transitionOn B S hS (fun _ : Unit => Y) (fun _ => g) (fun _ => F) (fun _ _ => φ) () () vik vi
        vk hik₀ hik₁ :=
  Iso.ext (by rw [Iso.trans_hom, transitionOn_hom, transitionOn_hom, transitionOn_hom]; exact h)

open QuasiCoherentDescent in
/-- The descent datum relative to a single morphism given by a quasi-coherent module and an
isomorphism satisfying the cocycle condition read through two-sided restriction. -/
noncomputable def descentDatumOfIso (g : Y ⟶ X) {F : Modules.{u, u} B S hS Y.1 Y.2}
    (hF : F.IsQuasicoherentOnSite)
    (φ : (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F ≅
      (modulePullback B S hS (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F)
    (hφ : ∀ (T : AlgebraicSpaces B S hS) (vi vj vk : T ⟶ Y)
      (vij vjk vik : T ⟶ pair B S hS (fun _ : Unit => Y) (fun _ => g) () ())
      (hij₀ : vij ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hij₁ : vij ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₀ : vjk ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk)
      (hik₀ : vik ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hik₁ : vik ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk),
      moduleHomRestrict₂ F F vij _ _ vi vj hij₀ hij₁ φ.hom ≫
          moduleHomRestrict₂ F F vjk _ _ vj vk hjk₀ hjk₁ φ.hom =
        moduleHomRestrict₂ F F vik _ _ vi vk hik₀ hik₁ φ.hom) :
    DescentDatum B S hS (fun _ : Unit => Y) (fun _ => g) where
  F := fun _ => F
  quasicoherent := fun _ => hF
  transition := fun _ _ => φ
  cocycle := fun _ _ _ T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ =>
    transitionOn_unit_trans B S hS g φ T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁
      (hφ T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)

open QuasiCoherentDescent in
/-- **Every descent datum relative to an étale covering is effective (Stacks 04W6).** -/
theorem isEtaleEffective_of_isEtaleCovering {I : Type*} (Yi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    (D : DescentDatum B S hS Yi f) : IsEtaleEffective B S hS Yi f hf D := by
  have := isCoverDense_memberFunctor B S hS Yi f hf hcov
  obtain ⟨M, hM, τ, hT⟩ := exists_memberReading B S hS Yi f hf D
  exact isEtaleEffective_of_memberReading B S hS Yi f hf D M hM τ hT

open QuasiCoherentDescent in
/-- The component isomorphism of an isomorphism of descent data. -/
noncomputable def DescentDatum.isoApp {I : Type*} {Yi : I → AlgebraicSpaces B S hS}
    {f : ∀ i, Yi i ⟶ X} {D E : DescentDatum B S hS Yi f} (e : D ≅ E) (i : I) : D.F i ≅ E.F i where
  hom := e.hom.app i
  inv := e.inv.app i
  hom_inv_id := (DescentDatum.comp_app e.hom e.inv i).symm.trans
    ((congrArg (fun z => DescentDatum.Hom.app z i) e.hom_inv_id).trans (DescentDatum.id_app _ i))
  inv_hom_id := (DescentDatum.comp_app e.inv e.hom i).symm.trans
    ((congrArg (fun z => DescentDatum.Hom.app z i) e.inv_hom_id).trans (DescentDatum.id_app _ i))

open QuasiCoherentDescent in
/-- A morphism `e` from `descentDatumOfIso` to the canonical descent datum of a quasi-coherent
module `M` on `X` carries `φ` to the canonical comparison of the two inverse images of `M`. -/
theorem descentDatumOfIso_naturality (g : Y ⟶ X) (hg : ∀ _ : Unit, IsEtale B S hS g.hom)
    {F : Modules.{u, u} B S hS Y.1 Y.2}
    (hF : F.IsQuasicoherentOnSite)
    (φ : (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F ≅
      (modulePullback B S hS (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F)
    (hφ : ∀ (T : AlgebraicSpaces B S hS) (vi vj vk : T ⟶ Y)
      (vij vjk vik : T ⟶ pair B S hS (fun _ : Unit => Y) (fun _ => g) () ())
      (hij₀ : vij ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hij₁ : vij ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₀ : vjk ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk)
      (hik₀ : vik ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hik₁ : vik ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk),
      moduleHomRestrict₂ F F vij _ _ vi vj hij₀ hij₁ φ.hom ≫
          moduleHomRestrict₂ F F vjk _ _ vj vk hjk₀ hjk₁ φ.hom =
        moduleHomRestrict₂ F F vik _ _ vi vk hik₀ hik₁ φ.hom)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (e : descentDatumOfIso B S hS g hF φ hφ ⟶
      etaleCanonicalDescentDatum B S hS (fun _ : Unit => Y) (fun _ => g) hg M hM) :
    (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).map (e.app ()) ≫
        (canonicalComparison (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())
          (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ()) g g
          (pair_condition B S hS (fun _ : Unit => Y) (fun _ => g) () ()) M).hom =
      φ.hom ≫ (modulePullback B S hS
        (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).map (e.app ()) := by
  have h := e.naturality () ()
  have e₁ := etaleCanonicalDescentDatum_transition B S hS (fun _ : Unit => Y) (fun _ => g) hg M hM
    () ()
  have e₂ : (descentDatumOfIso B S hS g hF φ hφ).transition () () = φ := rfl
  exact (congrArg (fun z => _ ≫ Iso.hom z) e₁.symm).trans
    (h.trans (congrArg (fun z => Iso.hom z ≫ _) e₂))

open QuasiCoherentDescent in
/-- **Descent of finitely presented modules along a surjective étale morphism (Stacks 04W6).**
Let `g : Y ⟶ X` be étale and surjective, `F` a finitely presented `𝒪_Y`-module and
`φ : pr₁^*F ≅ pr₂^*F` an isomorphism on `Y ×_X Y` whose restrictions to every triple of
morphisms into `Y` with equal composites to `X` satisfy the cocycle condition.  Then `F` is the
inverse image of a finitely presented `𝒪_X`-module `M`, through an isomorphism `α` which carries
`φ` to the canonical comparison of the two inverse images of `M`. -/
theorem exists_descent_of_isEtale (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Y.1) (fun _ => g.hom))
    (hsurj : IsSurjective B S hS g.hom) {F : Modules.{u, u} B S hS Y.1 Y.2}
    (hF : F.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F ⟶
      (modulePullback B S hS (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F)
    (φ' : (modulePullback B S hS (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F ⟶
      (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).obj F)
    (h₁ : φ ≫ φ' = 𝟙 _) (h₂ : φ' ≫ φ = 𝟙 _)
    (hφ : ∀ (T : AlgebraicSpaces B S hS) (vi vj vk : T ⟶ Y)
      (vij vjk vik : T ⟶ pair B S hS (fun _ : Unit => Y) (fun _ => g) () ())
      (hij₀ : vij ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hij₁ : vij ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₀ : vjk ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vj)
      (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk)
      (hik₀ : vik ≫ pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () () = vi)
      (hik₁ : vik ≫ pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () () = vk),
      moduleHomRestrict₂ F F vij _ _ vi vj hij₀ hij₁ φ ≫
          moduleHomRestrict₂ F F vjk _ _ vj vk hjk₀ hjk₁ φ =
        moduleHomRestrict₂ F F vik _ _ vi vk hik₀ hik₁ φ) :
    ∃ (M : Modules.{u, u} B S hS X.1 X.2) (_ : M.IsFinitePresentationOnSite)
      (α : F ≅ (modulePullback B S hS g).obj M),
      (modulePullback B S hS (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())).map α.hom ≫
          (canonicalComparison (pairFst B S hS (fun _ : Unit => Y) (fun _ => g) () ())
            (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ()) g g
            (pair_condition B S hS (fun _ : Unit => Y) (fun _ => g) () ()) M).hom =
        φ ≫ (modulePullback B S hS
          (pairSnd B S hS (fun _ : Unit => Y) (fun _ => g) () ())).map α.hom := by
  have hf : ∀ _ : Unit, IsEtale B S hS g.hom := fun _ => hg
  obtain ⟨M', hM', ⟨e⟩⟩ := isEtaleEffective_of_isEtaleCovering B S hS (fun _ : Unit => Y)
    (fun _ => g) hf hcov (descentDatumOfIso B S hS g (inferInstance : F.IsQuasicoherentOnSite)
      ⟨φ, φ', h₁, h₂⟩ hφ)
  let α : F ≅ (modulePullback B S hS g).obj M' := DescentDatum.isoApp B S hS e ()
  have hfp : ((etaleModulePullback B S hS g hg).obj M').IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS g hg).app M')
      (SheafOfModules.IsFinitePresentationOnSite.of_iso α hF)
  exact ⟨M', isFinitePresentationOnSite_of_etaleModulePullback B S hS g hg hsurj M' hfp, α,
    descentDatumOfIso_naturality B S hS g hf _ ⟨φ, φ', h₁, h₂⟩ hφ hM' e.hom⟩

end AlgebraicGeometry.Space

end
