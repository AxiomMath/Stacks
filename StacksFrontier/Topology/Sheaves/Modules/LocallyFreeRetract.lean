module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# A direct summand of a finite locally free sheaf of modules is finite locally free

Let `(X, 𝒪_X)` be a ringed space whose stalks `𝒪_{X,x}` are local rings, and let `H` be a
finite locally free sheaf of `𝒪_X`-modules. A direct summand `F` of `H` — a categorical
`CategoryTheory.Retract` of `H` in the category of sheaves of modules — is again finite locally
free.

The argument is the one of the source, in three steps. First, `F` is of finite presentation: a
retract of a free sheaf of modules on a finite index set is the cokernel of the idempotent
complementary to the retraction, which presents it by finitely many generators and finitely many
relations; applying this on the members of a local free presentation of `H` turns a retract of
`H` into a sheaf with finite quasi-coherent presentation data. Second, at every point the stalk
`F_x` is a free module of finite rank: it is a retract of `H_x`, which is finite free because
`H` is trivialised near `x`, so `F_x` is finite and flat, and a finite flat module over a local
ring is free. Third, [Stacks, Tag 0B8J] upgrades each of those free stalks to a free restriction
of `F` on an open neighbourhood, and those neighbourhoods cover `X`.

## Main results

* `AlgebraicGeometry.SheafOfModules.presentationOfRetractFree` — the presentation of a retract
  of a free sheaf of modules by the idempotent complementary to the retraction.
* `AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_retract` — a retract of a finite
  locally free sheaf of modules on a topological site is of finite presentation.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_retract` — **[Stacks, Tag 0BCI]**.

## Implementation notes

`CategoryTheory.Category (SheafOfModules R)` cannot be synthesised at the concrete site
`Opens X`: the hom-universe of `SheafOfModules.instCategory` is a `max`, and the unification
`max ?a ?b ≟ u` fails. The instance is therefore installed as a `local instance` with its levels
written out, which is what lets the ordinary `≫`/`𝟙`/projection notation be used below. Nothing
escapes the file, and at this site there is no competing route to the instance.

The stalk of a sheaf of modules over `𝒪_X` carries two actions of scalars that are not the same
term: one over the `RingCat`-valued stalk of `LocallyFreeRank.toRingSheaf X O`, which is what
[Stacks, Tag 0B8J] is stated over, and one over the `CommRingCat`-valued stalk of `O`, which is
what `LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp` and the local-ring hypothesis are
stated over. `SemilinearStalk.commStalkRingEquiv` identifies the two rings and
`commStalkRingEquiv_smul_eq'` below says the actions correspond, so the freeness obtained over the
second is transported to the first by `linearEquivFinsuppOfRingEquiv`.

`commStalkRingEquiv_smul_eq'` is `SemilinearStalk.comm_smul_eq` for a *sheaf* of commutative
rings, reproved rather than derived. The reproof is no longer forced — the remark it used to
carry, that `comm_smul_eq` was monomorphic at `TopCat.{0}`, is out of date now that
`Topology/Sheaves/Functors/Module/SemilinearStalk.lean` declares `universe u` — so this
declaration is a candidate for collapsing onto `SemilinearStalk.comm_smul_eq O.obj`. What was
recorded against doing so is a heartbeat finding rather than a universe one: pulling the
further instances of `AlgebraicGeometry/Divisors/AssociatedPoints/` into scope made
`isFiniteLocallyFree_of_retract` die with a `whnf` heartbeat timeout, with no other change to
the file.

The rank theory of [Stacks, Tag 01C9] is not needed, although the source's argument goes through
it. What the stalk computation requires of a trivialisation of `H` near `x` is only that its
index set be finite, and taking the trivialisation that the finite locally free data of `H`
itself provides on a cover member containing `x` makes that immediate: the index set is then
`(q.generators j).I`, finite by `q.IsFiniteType`. So no well-definedness of the rank, and hence
no nontriviality hypothesis on the stalks, enters.

## References

* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

/-! ### The presentation of a retract of a finite free sheaf of modules -/

section Presentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A retract of a free sheaf of modules is the cokernel of the idempotent complementary to the
retraction, which presents it on the retraction's index set. -/
def presentationOfRetractFree {F : _root_.SheafOfModules.{u} R} {I : Type u}
    (h : Retract F (_root_.SheafOfModules.free I)) : F.Presentation := by
  let f := 𝟙 (_root_.SheafOfModules.free (R := R) I) - h.r ≫ h.i
  have hfg : f ≫ h.r = 0 := by simp [f, h.retract]
  exact _root_.SheafOfModules.presentationOfIsCokernelFree f h.r hfg <|
    Limits.CokernelCofork.IsColimit.ofπ h.r hfg
      (fun k _ ↦ h.i ≫ k)
      (fun k hk ↦ by
        change (𝟙 _ - h.r ≫ h.i) ≫ k = 0 at hk
        rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at hk
        simpa only [Category.assoc] using hk.symm)
      (fun k _ m hm ↦ by
        rw [← Category.id_comp m, ← h.retract, Category.assoc, hm])

/-- The presentation of a retract of a free sheaf of modules on a finite index set is finite. -/
instance presentationOfRetractFree_isFinite {F : _root_.SheafOfModules.{u} R} {I : Type u}
    [Finite I] (h : Retract F (_root_.SheafOfModules.free I)) :
    (presentationOfRetractFree h).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite I)⟩

/-- `SheafOfModules.free.generatingSections I` has an invertible evaluation morphism. This is
Mathlib's instance, named here at an abstract site: at the concrete site `Opens X` the hom-universe
`max` of `SheafOfModules.instCategory` blocks the synthesis (see the implementation notes), and a
named general lemma can be applied there positionally. -/
theorem isIso_free_generatingSections_π (I : Type u) :
    IsIso (_root_.SheafOfModules.free.generatingSections (R := R) I).π :=
  inferInstance

end Presentation

/-! ### Transporting a finsupp presentation along a ring equivalence of the scalars -/

/-- A finsupp presentation of a module over one ring transports to a finsupp presentation over
an isomorphic ring whose action on the module agrees with it. -/
def linearEquivFinsuppOfRingEquiv {S A M ι : Type u} [CommRing S] [CommRing A]
    [AddCommGroup M] [Module S M] [Module A M] (eR : S ≃+* A)
    (hscalar : ∀ (s : S) (m : M), eR s • m = s • m) (e : M ≃ₗ[A] (ι →₀ A)) :
    M ≃ₗ[S] (ι →₀ S) := by
  letI : Module S A := Module.compHom A eR.toRingHom
  letI : Module S (ι →₀ A) := inferInstance
  let e' : M ≃ₗ[S] (ι →₀ A) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun s m ↦ by
        calc e (s • m) = e (eR s • m) := by rw [hscalar]
          _ = eR s • e m := e.map_smul _ _
          _ = s • e m := rfl }
  let ce : A ≃ₗ[S] S :=
    { toFun := eR.symm
      invFun := eR
      left_inv := eR.apply_symm_apply
      right_inv := eR.symm_apply_apply
      map_add' := eR.symm.map_add
      map_smul' := fun s a ↦ by
        change eR.symm (eR s * a) = s * eR.symm a
        apply eR.injective
        simp }
  exact e'.trans (Finsupp.mapRange.linearEquiv (α := ι) ce)

/-- The `CommRingCat`-valued and `RingCat`-valued stalk actions on the stalk of a presheaf of
modules agree through `SemilinearStalk.commStalkRingEquiv`. This is
`SemilinearStalk.comm_smul_eq` for a sheaf of commutative rings, reproved; see the
implementation notes. -/
theorem commStalkRingEquiv_smul_eq' {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X) (x : X)
    (M : PresheafOfModules.{u} (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (s : TopCat.Presheaf.stalk (C := RingCat.{u})
      (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :
    SemilinearStalk.commStalkRingEquiv O.obj x s • m = s • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq
    (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) s
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  set rr : ToType (O.obj.obj (op (U₁ ⊓ U₂))) :=
    (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map (homOfLE inf_le_left).op r₀ with hrr
  set mm : ToType (M.presheaf.obj (op (U₁ ⊓ U₂))) :=
    M.presheaf.map (homOfLE inf_le_right).op m₀ with hmm
  have hr' : TopCat.Presheaf.germ (C := RingCat.{u})
      (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (U₁ ⊓ U₂) x hmem rr = s := by
    simpa only [hrr, TopCat.Presheaf.germ_res_apply] using hr
  have hm' : TopCat.Presheaf.germ M.presheaf (U₁ ⊓ U₂) x hmem mm = m := by
    simpa only [hmm, TopCat.Presheaf.germ_res_apply] using hm
  rw [← hr', ← hm', SemilinearStalk.commStalkRingEquiv_germ]
  exact (PresheafOfModules.germ_smul M x (U₁ ⊓ U₂) hmem rr mm).symm.trans
    (PresheafOfModules.germ_ringCat_smul M x (U₁ ⊓ U₂) hmem rr mm)

/-! ### Finite presentation of a retract -/

section Space

variable {X : TopCat.{u}}

/-- `CategoryTheory.Category (SheafOfModules R)` at the concrete site `Opens X`. Instance
search cannot produce it there, because the hom-universe of `SheafOfModules.instCategory` is a
`max` and `max ?a ?b ≟ u` does not unify; writing the levels out fixes it. -/
local instance categorySheafOfModules (R : TopCat.Sheaf RingCat.{u} X) :
    Category.{u} (_root_.SheafOfModules.{u} R) :=
  _root_.SheafOfModules.instCategory.{u, u, u, u}

variable {R : TopCat.Sheaf RingCat.{u} X}

/-- The two legs of a retract of sheaves of modules split each other on every stalk. -/
theorem stalkLMap_retract_comp {F H : _root_.SheafOfModules.{u} R} (h : Retract F H) (x : X) :
    (LocallyFreeRank.stalkLMap h.r.val x).comp (LocallyFreeRank.stalkLMap h.i.val x) =
      LinearMap.id := by
  have hval : h.i.val ≫ h.r.val = 𝟙 F.val :=
    congrArg _root_.SheafOfModules.Hom.val h.retract
  have hmorph :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map h.i.val) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map h.r.val) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  exact LinearMap.ext fun m ↦
    (ConcreteCategory.comp_apply (C := AddCommGrpCat.{u}) _ _ m).symm.trans
      ((congrArg (fun φ ↦ (ConcreteCategory.hom φ) m) hmorph).trans
        (ConcreteCategory.id_apply (C := AddCommGrpCat.{u}) m))

/-- The trivialisation of a locally free sheaf of modules carried by a member of its own
local-generator data: on `q.X i` the restriction of `F` is isomorphic to the free sheaf on
`(q.generators i).I`. -/
def localGeneratorsTrivialization (R : TopCat.Sheaf RingCat.{u} X)
    (F : _root_.SheafOfModules.{u} R) (q : _root_.SheafOfModules.LocalGeneratorsData.{u} F)
    (hq : q.IsLocallyFreeData) (i : q.I) :
    LocallyFreeRank.Trivialization X R F (q.X i) := by
  haveI : IsIso (q.generators i).π := hq.isIso i
  let U := q.X i
  let E := U.sheafOfModulesEquivOver R
  let e : _root_.SheafOfModules.free (q.generators i).I ≅ F.over U := asIso (q.generators i).π
  let eFree : _root_.SheafOfModules.free (q.generators i).I ≅
      E.functor.obj (_root_.SheafOfModules.free (q.generators i).I) :=
    _root_.SheafOfModules.mapFreeIso E.functor (q.generators i).I
      (U.sheafOfModulesEquivOverUnit R)
  exact ⟨(q.generators i).I, (eFree ≪≫ E.functor.mapIso e ≪≫
    LocallyFreeRank.restrictModIsoOver X U R F).symm⟩

/-- A retract of a finite locally free sheaf of modules is of finite presentation. -/
theorem isFinitePresentation_of_retract {F H : _root_.SheafOfModules.{u} R} (hF : Retract F H)
    (hH : @IsFiniteLocallyFree (Opens X) inferInstance (Opens.grothendieckTopology X) R
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) H) :
    @_root_.SheafOfModules.IsFinitePresentation (Opens X) inferInstance
      (Opens.grothendieckTopology X) R (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) F := by
  classical
  obtain ⟨q, hq, hqf⟩ := hH.exists_isFiniteLocallyFreeData
  let _ : q.IsLocallyFreeData := hq
  let _ : q.IsFiniteType := hqf
  let σ : F.QuasicoherentData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      presentation j := by
        have : IsIso (q.generators j).π := hq.isIso j
        let hFU := Retract.map hF (_root_.SheafOfModules.overFunctor R (q.X j))
        let hfree : Retract (F.over (q.X j))
            (_root_.SheafOfModules.free (q.generators j).I) :=
          { i := hFU.i ≫ inv (q.generators j).π
            r := (q.generators j).π ≫ hFU.r
            retract := by
              rw [Category.assoc, ← Category.assoc (inv (q.generators j).π),
                IsIso.inv_hom_id, Category.id_comp]
              exact hFU.retract }
        exact presentationOfRetractFree hfree }
  refine { exists_quasicoherentData := ⟨σ,
    _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.mk.{u, u, u, u}
      (q := σ) fun j ↦ ?_⟩ }
  dsimp only [σ]
  let _ : Finite (q.generators j).I := (hqf.isFiniteType j).finite
  infer_instance

end Space

/-! ### Tag 0BCI -/

section Main

variable {X : TopCat.{u}} {O : TopCat.Sheaf CommRingCat.{u} X}

/-- The category structure on sheaves of modules over the ring sheaf underlying `O`. -/
local instance categorySheafOfModulesToRingSheaf :
    Category.{u} (_root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)) :=
  _root_.SheafOfModules.instCategory.{u, u, u, u}

/-- At every point, the stalk of a retract of a finite locally free sheaf of modules on a
ringed space with local stalks is a free module of finite rank over the stalk of the ring sheaf.
-/
theorem exists_free_stalk_of_retract
    [∀ x : X, IsLocalRing (ToType (TopCat.Presheaf.stalk O.obj x))]
    {F H : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)}
    (h : Retract F H)
    (hH : @IsFiniteLocallyFree (Opens X) inferInstance (Opens.grothendieckTopology X)
      (LocallyFreeRank.toRingSheaf X O) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) H)
    (x : X) :
    ∃ r : ℕ, Nonempty
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x) ≃ₗ[
        ToType (TopCat.Presheaf.stalk
          (C := RingCat.{u}) (LocallyFreeRank.toRingSheaf X O).obj x)]
        (ULift.{u} (Fin r) →₀
          ToType (TopCat.Presheaf.stalk
            (C := RingCat.{u}) (LocallyFreeRank.toRingSheaf X O).obj x))) := by
  classical
  let S := ToType (TopCat.Presheaf.stalk
    (C := RingCat.{u}) (LocallyFreeRank.toRingSheaf X O).obj x)
  let A := ToType (TopCat.Presheaf.stalk O.obj x)
  let eR : S ≃+* A := SemilinearStalk.commStalkRingEquiv O.obj x
  let _ : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b ↦ eR.injective (by simp only [map_mul, mul_comm]) }
  let _ : IsLocalRing S := eR.symm.isLocalRing
  let _ : Module A (ToType (TopCat.Presheaf.stalk H.val.presheaf x)) :=
    LocallyFreeRank.instModuleStalkF X O H x
  obtain ⟨q, hq, hqf⟩ := hH.exists_isFiniteLocallyFreeData
  obtain ⟨j, hxj⟩ := ((Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop).exists_mem x
  let t := localGeneratorsTrivialization (LocallyFreeRank.toRingSheaf X O) H q hq j
  let _ : Finite t.ι := (hqf.isFiniteType j).finite
  obtain ⟨eH⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X O H x hxj t
  have hscalar : ∀ (s : S) (m : ToType (TopCat.Presheaf.stalk H.val.presheaf x)),
      eR s • m = s • m := fun s m ↦ commStalkRingEquiv_smul_eq' O x H.val s m
  let bH := (Finsupp.basisSingleOne (R := S) (ι := t.ι)).map
    (linearEquivFinsuppOfRingEquiv eR hscalar eH).symm
  let _ : Module.Free S (ToType (TopCat.Presheaf.stalk H.val.presheaf x)) :=
    Module.Free.of_basis bH
  let _ : Module.Finite S (ToType (TopCat.Presheaf.stalk H.val.presheaf x)) :=
    Module.Finite.of_basis bH
  have hsplit : (LocallyFreeRank.stalkLMap h.r.val x).comp
      (LocallyFreeRank.stalkLMap h.i.val x) = LinearMap.id :=
    stalkLMap_retract_comp h x
  have hsurj : Function.Surjective (LocallyFreeRank.stalkLMap h.r.val x) := fun y ↦
    ⟨LocallyFreeRank.stalkLMap h.i.val x y, congrArg (fun φ ↦ φ y) hsplit⟩
  let _ : Module.Flat S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.Flat.of_retract _ _ hsplit
  let _ : Module.Finite S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.Finite.of_surjective _ hsurj
  let _ : Module.Free S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨(Module.finBasis S (ToType (TopCat.Presheaf.stalk F.val.presheaf x))).repr.trans
    (Finsupp.domLCongr Equiv.ulift.symm)⟩⟩

/-- **Stacks Project, Tag 0BCI.** A direct summand of a finite locally free sheaf of modules on
a ringed space whose stalks are local rings is finite locally free.

The tag attribute for 0BCI belongs on this declaration and on no other: the tag's covering set
is this one statement. It is deliberately not placed here, attribute placement being the lead's.
-/
@[stacks 0BCI, sga "6 I 2.15.1" "ringed space case"]
theorem isFiniteLocallyFree_of_retract
    [∀ x : X, IsLocalRing (ToType (TopCat.Presheaf.stalk O.obj x))]
    {F H : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)}
    (hF : Nonempty (Retract F H))
    (hH : @IsFiniteLocallyFree (Opens X) inferInstance (Opens.grothendieckTopology X)
      (LocallyFreeRank.toRingSheaf X O) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) H) :
    @IsFiniteLocallyFree (Opens X) inferInstance (Opens.grothendieckTopology X)
      (LocallyFreeRank.toRingSheaf X O) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) F := by
  classical
  obtain ⟨h⟩ := hF
  have hfp := isFinitePresentation_of_retract h hH
  let _ : F.IsFinitePresentation := hfp
  have hchart (x : X) : ∃ U : Opens X, ∃ r : ℕ, x ∈ U ∧
      Nonempty (F.over U ≅ _root_.SheafOfModules.free (ULift.{u} (Fin r))) := by
    obtain ⟨r, hx⟩ := exists_free_stalk_of_retract h hH x
    obtain ⟨U, hxU, e⟩ :=
      Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free F hfp x r hx
    exact ⟨U, r, hxU, e⟩
  choose U r hxU he using hchart
  let q : F.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff (X : Type u) U).mpr
        (TopologicalSpace.IsOpenCover.mk (top_unique fun x _ ↦
          TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩))
      generators := fun x ↦
        (_root_.SheafOfModules.free.generatingSections (ULift.{u} (Fin (r x)))).ofEpi
          (he x).some.inv }
  have hlf : q.IsLocallyFreeData := by
    constructor
    intro x
    dsimp only [q]
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_free_generatingSections_π (ULift.{u} (Fin (r x)))) inferInstance
  have hft : q.IsFiniteType := by
    constructor
    intro x
    dsimp only [q]
    constructor
    change Finite (ULift.{u} (Fin (r x)))
    infer_instance
  exact { exists_isFiniteLocallyFreeData := ⟨q, hlf, hft⟩ }

end Main

end AlgebraicGeometry.SheafOfModules

end
