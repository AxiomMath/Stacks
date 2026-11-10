module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsLocalPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThreeToTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect

/-!
# A chain-level tensor pairing of strictly perfect complexes gives paired splittings

Let `(C, O)` be a ringed site and `P`, `P'` complexes of `O`-modules whose terms are direct
summands of finite free modules, and let `W` be an object of `C`. If over `W` the total tensor
complex `Tot(P ⊗ P')` is homotopy equivalent to `O[0]`, then `P` and `P'` carry a paired
splitting over `W`: this is the ring-level structure of invertible objects (Stacks 0FNT) on the
global sections of the localized ringed site `(C/W, O|_W)`, carried back to the sheaves.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.SheafOfModules.DerivedMonoidal Stacks.Cohomology.SiteModules

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

variable {Z : RingedSite.{u, u, u}} [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Z.C, HasSheafify (Z.J.over W) AddCommGrpCat.{u}]
  [∀ W : Z.C, (Z.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Evaluation of a global section of the localized site at the terminal object. -/
abbrev evalTop {W : Z.C} (r : GammaRing (Z.over W)) : (Z.O.obj.obj (op W) : Type u) :=
  r.1 (op (Over.mk (𝟙 W)))

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Z.C, HasSheafify (Z.J.over W) AddCommGrpCat.{u}]
  [∀ W : Z.C, (Z.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restricting the value at the terminal object along `g` is the value at `g`. -/
theorem map_evalTop {W W' : Z.C} (g : W' ⟶ W) (r : GammaRing (Z.over W)) :
    Z.O.obj.map g.op (evalTop r) = r.1 (op (Over.mk g)) :=
  r.2 (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 W)).op

/-- `evalTop` is a ring homomorphism. -/
def evalTopHom (W : Z.C) : GammaRing (Z.over W) →+* (Z.O.obj.obj (op W) : Type u) :=
  globalSectionEvalHom (Z.over W).O (op (Over.mk (𝟙 W)))

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Z.C, HasSheafify (Z.J.over W) AddCommGrpCat.{u}]
  [∀ W : Z.C, (Z.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Multiplication by a global section of the localized site is, on sections of a restricted
module, multiplication by its value. -/
theorem smul_of_smulHom_eq {W : Z.C} {G : Mod (Z.over W).O} {r : GammaRing (Z.over W)}
    {p : Prop} [Decidable p] (h : smulHom (toGS r) G = if p then 𝟙 _ else 0) {W' : Z.C}
    (g : W' ⟶ W) (m : G.val.obj (op (Over.mk g))) :
    ringSec (r.1 (op (Over.mk g))) • m = if p then m else 0 := by
  refine (congrArg (fun φ : G ⟶ G => φ.val.app (op (Over.mk g)) m) h).trans ?_
  split_ifs <;> rfl

/-- Presheaves of abelian groups on the localized ringed site `Z.over W` admit sheafification. -/
instance hasSheafify_over' (W : Z.C) : HasSheafify (Z.over W).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Z.J.over W) AddCommGrpCat.{u})

/-- On the localized ringed site `Z.over W`, the morphisms of abelian-group presheaves inverted
by sheafification are exactly the locally bijective ones. -/
instance wEqualsLocallyBijective_over' (W : Z.C) :
    (Z.over W).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((Z.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u})

variable (Z) in
/-- Restriction of `O`-modules to the localized ringed site `(C/W, O|_W)`, written with the
structure sheaf of the localized site. -/
abbrev ovF (W : Z.C) : Mod Z.O ⥤ Mod (Z.over W).O :=
  SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) W

/-- Restriction of `O`-modules to the localized ringed site is additive. -/
instance ovF_additive (W : Z.C) : (ovF Z W).Additive :=
  inferInstanceAs
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) W).Additive

/-- Restriction of `O`-modules to the localized ringed site preserves homology of short
complexes. -/
instance ovF_preservesHomology (W : Z.C) : (ovF Z W).PreservesHomology :=
  preservesHomology_overFunctor' (X := Z) W

/-- The restriction of a complex of `O`-modules to the localized ringed site. -/
abbrev restrictMod (E : CochainComplex (Mod Z.O) ℤ) (W : Z.C) :
    CochainComplex (Mod (Z.over W).O) ℤ :=
  ((ovF Z W).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- The cohomology of the restriction is the restriction of the cohomology. -/
def restrictModHomologyIso (E : CochainComplex (Mod Z.O) ℤ) (W : Z.C) (k : ℤ) :
    (restrictMod E W).homology k ≅ (ovF Z W).obj (E.homology k) :=
  (E.sc k).mapHomologyIso (ovF Z W)

/-- An isomorphism of sheaves of modules followed by its inverse is the identity on sections. -/
private theorem inv_val_app_hom_val_app {Y : RingedSite.{u, u, u}} {G H : Mod Y.O} (e : G ≅ H)
    (U : Y.Cᵒᵖ) (x : G.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x := by
  change (e.hom ≫ e.inv).val.app U x = x
  rw [Iso.hom_inv_id]
  rfl

/-- The inverse of an isomorphism of sheaves of modules followed by it is the identity on
sections. -/
private theorem hom_val_app_inv_val_app {Y : RingedSite.{u, u, u}} {G H : Mod Y.O} (e : G ≅ H)
    (U : Y.Cᵒᵖ) (x : H.val.obj U) : e.hom.val.app U (e.inv.val.app U x) = x := by
  change (e.inv ≫ e.hom).val.app U x = x
  rw [Iso.inv_hom_id]
  rfl


/-- An isomorphism of sheaves of modules is bijective on sections. -/
private theorem bijective_val_app_hom {Y : RingedSite.{u, u, u}} {G H : Mod Y.O} (e : G ≅ H)
    (U : Y.Cᵒᵖ) : Function.Bijective (e.hom.val.app U) :=
  ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).map e.hom)

/-- A global section acting on a module by `1` or `0` acts the same way on an isomorphic one. -/
private theorem smulHom_eq_ite_of_iso {Y : RingedSite.{u, u, u}} (s : GlobalSection Y)
    {G H : Mod Y.O} (e : G ≅ H) {p : Prop} [Decidable p] (h : smulHom s G = if p then 𝟙 _ else 0) :
    smulHom s H = if p then 𝟙 _ else 0 := by
  have h1 := smulHom_naturality s e.hom
  rw [h] at h1
  rw [← cancel_epi e.hom, h1]
  split_ifs <;> simp

/-- **A chain-level tensor pairing over `W` gives a paired splitting over `W`.** -/
theorem nonempty_pairedSplitting_of_homotopyEquiv (E F : CochainComplex (Mod Z.O) ℤ) (W : Z.C)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ ((restrictMod E W).X i))
    (hF : ∀ i, _root_.IsDirectSummandOfFiniteFree _ ((restrictMod F W).X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero ((restrictMod E W).X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero ((restrictMod F W).X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor (restrictMod E W) (restrictMod F W)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over W).O) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    Nonempty (PairedSplitting E F W) := by
  obtain ⟨S, f, fidem, fortho, fzero, fsum, hsE, hsF, faith, pair⟩ :=
    exists_sheaf_splitting (Z.over W) (restrictMod E W) (restrictMod F W) hE hF
      a b a' b' hEz hFz h
  let Θ := fun k => restrictModHomologyIso E W k
  let Θ' := fun k => restrictModHomologyIso F W k
  refine ⟨{ T := S
            f := fun n => evalTop (f n)
            idem := fun n => (fidem n).map (evalTopHom W)
            ortho := fun n m hnm => by
              have := congrArg (evalTopHom W) (fortho n m hnm)
              rwa [map_mul, map_zero] at this
            eq_zero := fun n hn => by
              have := congrArg (evalTopHom W) (fzero n hn)
              rwa [map_zero] at this
            sum_eq_one := by
              have := congrArg (evalTopHom W) fsum
              rwa [map_sum, map_one] at this
            smul := fun n k W' g m => by
              rw [map_evalTop]
              exact smul_of_smulHom_eq (smulHom_eq_ite_of_iso _ (Θ k) (hsE n k)) g m
            faithful := fun W' g t ht => ?_
            smul' := fun n k W' g m => by
              rw [map_evalTop]
              exact smul_of_smulHom_eq (smulHom_eq_ite_of_iso _ (Θ' k) (hsF n k)) g m
            gen := fun n => ?_ }⟩
  · refine faith (W := Over.mk g) t fun k m => ?_
    have h1 := ht k (𝟙 W') ((Θ k).hom.val.app (op (Over.mk g)) m)
    rw [op_id, Z.O.obj.map_id, ConcreteCategory.id_apply] at h1
    refine (bijective_val_app_hom (Θ k) (op (Over.mk g))).1 ?_
    rw [((Θ k).hom.val.app _).hom.map_smul, map_zero]
    exact h1
  · let e1 := sheafTensorOverIso Z W (E.homology n) (F.homology (-n))
    let e2 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over W).O).obj
          ((ovF Z W).obj (E.homology n))).obj ((ovF Z W).obj (F.homology (-n))) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over W).O).obj
          ((restrictMod E W).homology n)).obj ((restrictMod F W).homology (-n)) :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over W).O).mapIso
        (Θ n).symm).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over W).O).obj _).mapIso
          (Θ' (-n)).symm
    have hs : toGS (f n) * toGS (f n) = toGS (f n) :=
      GlobalSection.ext fun U => congrArg (fun r : GammaRing (Z.over W) => r.1 U) (fidem n).eq
    obtain ⟨t, ht⟩ := exists_gen_of_iso_splitObj (Y := Z.over W) (G := (ovF Z W).obj
      (pairingTensor E F n)) (toGS (f n)) hs (e1 ≪≫ e2 ≪≫ Classical.choice (pair n))
      (Over.mk (𝟙 W))
    refine ⟨t, fun W' g => ?_⟩
    let eq : {a : (Z.O.obj.obj (op W') : Type u) // Z.O.obj.map g.op (evalTop (f n)) * a = a} ≃
        {a : ((Z.over W).O.obj.obj (op (Over.mk g)) : Type u) //
          (toGS (f n)).val (op (Over.mk g)) * a = a} :=
      Equiv.subtypeEquivRight fun a => by
        rw [map_evalTop]
        rfl
    exact (ht (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 W))).comp eq.bijective

/-- **A derived pairing of strictly perfect complexes gives paired splittings on a covering of
every object.** Let `P`, `P'` be strictly perfect complexes of `O`-modules with `Tot(P ⊗ P')`
isomorphic to `O[0]` in `D(O)`. Then every object of the site has a covering by objects carrying
paired splittings of `P` and `P'`. -/
theorem pairedPresieve_mem (P P' : CochainComplex (Mod Z.O) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) P)
    (hP' : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) P')
    [HasDerivedCategory.{d} (Mod Z.O)]
    (γ : DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj P') ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))))
    (U : Z.C) : Sieve.generate (pairedPresieve P P' U) ∈ Z.J U := by
  let T := ((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj P'
  let O0 := (HomologicalComplex.single (Mod Z.O) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  let Fo := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U
  have hT := Stacks.SheafOfModules.Tensor.isStrictlyPerfect_tensorComplex Z.O P P' hP hP'
  have hO : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) O0 :=
    isStrictlyPerfect_structureSheafComplex Z
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits (R :=
    Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (R :=
    Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U
  have hTU := SheafOfModules.isStrictlyPerfect_map Fo (Iso.refl _) hT
  have hOU := SheafOfModules.isStrictlyPerfect_map Fo (Iso.refl _) hO
  let : HasDerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over U)) := HasDerivedCategory.standard _
  let φ := (Fo.mapDerivedCategoryFactors.app T).symm ≪≫ Fo.mapDerivedCategory.mapIso γ ≪≫
    Fo.mapDerivedCategoryFactors.app O0
  refine Z.J.superset_covering ?_ (homotopyEquivSieve_mem Z U hTU hOU φ)
  rintro W f ⟨h⟩
  refine ⟨W, 𝟙 W, f, ?_, Category.id_comp f⟩
  have : PreservesFiniteColimits (ovF Z W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (R :=
      Stacks.SheafOfModules.Tensor.ringSheaf Z.O) W
  let e1 : (restr Z f).obj ((Fo.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (Z.O.over W)).obj (restrictMod P W)).obj
        (restrictMod P' W) :=
    restrictComplexOverIso f T ≪≫ tensorComplexOverIso Z W P P'
  let e2 : (restr Z f).obj ((Fo.mapHomologicalComplex (ComplexShape.up ℤ)).obj O0) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _) :=
    restrictComplexOverIso f O0 ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (ovF Z W) (ComplexShape.up ℤ) 0).app _
  obtain ⟨a, b, hz⟩ := Stacks.Cohomology.InvertibleDerived.exists_bounds P hP.bounded
  obtain ⟨a', b', hz'⟩ := Stacks.Cohomology.InvertibleDerived.exists_bounds P' hP'.bounded
  exact nonempty_pairedSplitting_of_homotopyEquiv P P' W
    (fun i => SheafOfModules.isDirectSummandOfFiniteFree_map (ovF Z W) (Iso.refl _) _
      (hP.termDirectSummand i))
    (fun i => SheafOfModules.isDirectSummandOfFiniteFree_map (ovF Z W) (Iso.refl _) _
      (hP'.termDirectSummand i))
    a b a' b' (fun i hi => (ovF Z W).map_isZero (hz i hi))
    (fun i hi => (ovF Z W).map_isZero (hz' i hi))
    ((HomotopyEquiv.ofIso e1.symm).trans (h.trans (HomotopyEquiv.ofIso e2)))

/-! ### Transporting paired splittings -/

/-- A function agreeing pointwise with a composite `e ∘ g` of bijections is bijective. -/
theorem bijective_of_comp_eq {α β γ : Type*} {f : α → γ} {g : α → β} {e : β → γ}
    (he : Function.Bijective e) (hg : Function.Bijective g) (h : ∀ a, f a = e (g a)) :
    Function.Bijective f := by
  rw [funext h]
  exact he.comp hg

/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem bijective_app_of_iso {Y : RingedSite.{u, u, u}} {G H : Mod Y.O} (e : G ≅ H) (U : Y.Cᵒᵖ) :
    Function.Bijective (e.hom.val.app U) :=
  bijective_val_app_hom e U

/-- **Paired splittings transport along isomorphisms of the cohomology sheaves.** -/
def PairedSplitting.transport {Y : RingedSite.{u, u, u}} [HasSheafify Y.J AddCommGrpCat.{u}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] {E F E₂ F₂ : CochainComplex (Mod Y.O) ℤ}
    (α : ∀ k, E.homology k ≅ E₂.homology k) (β : ∀ k, F.homology k ≅ F₂.homology k) {W : Y.C}
    (A : PairedSplitting E F W) : PairedSplitting E₂ F₂ W where
  T := A.T
  f := A.f
  idem := A.idem
  ortho := A.ortho
  eq_zero := A.eq_zero
  sum_eq_one := A.sum_eq_one
  smul n k W' g m := by
    obtain ⟨m, rfl⟩ := (bijective_app_of_iso (α k) (op W')).2 m
    rw [← ((α k).hom.val.app (op W')).hom.map_smul, A.smul n k g m]
    split_ifs <;> simp
  faithful W' g t ht := A.faithful g t fun k W'' g'' m => by
    refine (bijective_app_of_iso (α k) (op W'')).1 ?_
    rw [((α k).hom.val.app (op W'')).hom.map_smul, map_zero]
    exact ht k g'' _
  smul' n k W' g m := by
    obtain ⟨m, rfl⟩ := (bijective_app_of_iso (β k) (op W')).2 m
    rw [← ((β k).hom.val.app (op W')).hom.map_smul, A.smul' n k g m]
    split_ifs <;> simp
  gen n := by
    obtain ⟨t, ht⟩ := A.gen n
    let ψ : pairingTensor E F n ≅ pairingTensor E₂ F₂ n :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).mapIso (α n)).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj _).mapIso (β (-n))
    refine ⟨ψ.hom.val.app (op W) t, fun W' g => ?_⟩
    refine bijective_of_comp_eq (bijective_app_of_iso ψ (op W')) (ht g) fun c => ?_
    exact (congrArg (ringSec c.1 • ·)
      (PresheafOfModules.naturality_apply ψ.hom.val g.op t).symm).trans
      ((ψ.hom.val.app (op W')).hom.map_smul _ _).symm

/-- **A paired splitting on the localized site descends.** A paired splitting over an object `W`
of `C/V` of two complexes on `(C/V, O|_V)` whose cohomology sheaves are those of `K` and `K'`
restricted to `C/V` is a paired splitting of `K` and `K'` over `W.left`. -/
def PairedSplitting.descend {K K' : CochainComplex (Mod Z.O) ℤ} {V : Z.C} {W : Over V}
    {E E' : CochainComplex (Mod (Z.over V).O) ℤ}
    (Θ : ∀ k, E.homology k ≅ (ovF Z V).obj (K.homology k))
    (Θ' : ∀ k, E'.homology k ≅ (ovF Z V).obj (K'.homology k))
    (A : PairedSplitting (X := Z.over V) E E' W) :
    PairedSplitting K K' W.left :=
  { T := A.T
    f := A.f
    idem := A.idem
    ortho := A.ortho
    eq_zero := A.eq_zero
    sum_eq_one := A.sum_eq_one
    smul := fun n k W' g m => by
      have h := A.smul n k (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W)
        ((Θ k).inv.val.app (op (Over.mk (g ≫ W.hom))) m)
      have h2 := congrArg ((Θ k).hom.val.app (op (Over.mk (g ≫ W.hom)))) h
      rw [((Θ k).hom.val.app _).hom.map_smul] at h2
      have h3 : (Θ k).hom.val.app (op (Over.mk (g ≫ W.hom)))
          ((Θ k).inv.val.app (op (Over.mk (g ≫ W.hom))) m) = m := by
        change ((Θ k).inv ≫ (Θ k).hom).val.app (op (Over.mk (g ≫ W.hom))) m = m
        rw [Iso.inv_hom_id]; rfl
      rw [h3] at h2
      refine h2.trans ?_
      split_ifs
      · exact h3
      · exact map_zero _
    faithful := fun W' g t ht => A.faithful (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W) t
      fun k W'' g'' m => by
        refine (bijective_app_of_iso (Θ k) (op W'')).1 ?_
        rw [((Θ k).hom.val.app (op W'')).hom.map_smul, map_zero]
        exact ht k g''.left _
    smul' := fun n k W' g m => by
      have h := A.smul' n k (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W)
        ((Θ' k).inv.val.app (op (Over.mk (g ≫ W.hom))) m)
      have h2 := congrArg ((Θ' k).hom.val.app (op (Over.mk (g ≫ W.hom)))) h
      rw [((Θ' k).hom.val.app _).hom.map_smul] at h2
      have h3 : (Θ' k).hom.val.app (op (Over.mk (g ≫ W.hom)))
          ((Θ' k).inv.val.app (op (Over.mk (g ≫ W.hom))) m) = m := by
        change ((Θ' k).inv ≫ (Θ' k).hom).val.app (op (Over.mk (g ≫ W.hom))) m = m
        rw [Iso.inv_hom_id]; rfl
      rw [h3] at h2
      refine h2.trans ?_
      split_ifs
      · exact h3
      · exact map_zero _
    gen := fun n => by
      obtain ⟨t, ht⟩ := A.gen n
      let ψ : pairingTensor (X := Z.over V) E E' n ≅
          (ovF Z V).obj (pairingTensor K K' n) :=
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over V).O).mapIso
          (Θ n)).app _ ≪≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over V).O).obj _).mapIso
            (Θ' (-n)) ≪≫ (sheafTensorOverIso Z V (K.homology n) (K'.homology (-n))).symm
      refine ⟨ψ.hom.val.app (op W) t, fun W' g => ?_⟩
      let g' : Over.mk (g ≫ W.hom) ⟶ W := Over.homMk g
      let eq : {a : (Z.O.obj.obj (op W') : Type u) // Z.O.obj.map g.op (A.f n) * a = a} ≃
          {a : ((Z.over V).O.obj.obj (op (Over.mk (g ≫ W.hom))) : Type u) //
            (Z.over V).O.obj.map g'.op (A.f n) * a = a} := Equiv.subtypeEquivRight fun a => Iff.rfl
      refine bijective_of_comp_eq (bijective_app_of_iso ψ (op (Over.mk (g ≫ W.hom))))
        ((ht g').comp eq.bijective) fun c => ?_
      exact (congrArg (ringSec c.1 • ·)
        (PresheafOfModules.naturality_apply ψ.hom.val g'.op t).symm).trans
        ((ψ.hom.val.app _).hom.map_smul _ _).symm }

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
