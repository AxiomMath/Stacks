module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InternalHomPairing

/-!
# The internal Hom of discrete `G`-modules

Let `G` be a topological group and `M`, `N` discrete `G`-modules with `M` finite. The group
`Hom_ℤ(M, N)` with the conjugation action `(g · φ)(m) = g · φ(g⁻¹ · m)` is again a discrete
`G`-module (`CategoryTheory.ContinuousGAddCommGrp.hom`): `φ` is fixed by the open subgroup of
elements fixing the finitely many points of `M` and their images.

A morphism of continuous `G`-sets `S ⟶ Hom_ℤ(M, N)` is the same thing as an equivariant map
`S × M ⟶ N` additive in `M`, read as a morphism of functors on the one-object category of `G`
(`CategoryTheory.ContinuousGAddCommGrp.homPairingEquiv`).

## Main definitions

* `CategoryTheory.ContinuousGAddCommGrp.hom` — `Hom_ℤ(M, N)` with the conjugation action.
* `CategoryTheory.ContinuousGAddCommGrp.homIsFinite` — the same for finite modules.
* `CategoryTheory.ContinuousGAddCommGrp.homPairingEquiv` — morphisms into `Hom_ℤ(M, N)` are
  pairings additive in the second variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u w

attribute [local instance] discreteForget₂Type discreteForget₂AddCommGrpCat

namespace CategoryTheory

namespace ContinuousGAddCommGrp

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The stabilizers of a discrete `G`-module are open.** -/
theorem isOpen_setOf_rho_apply_eq (M : ContinuousGAddCommGrp.{u, w} G) (x : M.obj.obj.V) :
    IsOpen {g : G | (M.obj.obj.ρ g).asHom.hom x = x} := by
  have hc := (Action.isContinuous_def M.obj.obj).mp M.obj.property
  have : DiscreteTopology ((forget₂ AddCommGrpCat TopCat).obj M.obj.obj.V) := ⟨rfl⟩
  have h : Continuous fun g : G ↦ (forget₂ AddCommGrpCat TopCat).map (M.obj.obj.ρ g).asHom x :=
    hc.comp (Continuous.prodMk continuous_id continuous_const)
  exact h.isOpen_preimage {x} (isOpen_discrete _)

/-- `g⁻¹` undoes the action of `g` on a discrete `G`-module. -/
lemma rho_inv_apply_rho_apply (M : ContinuousGAddCommGrp.{u, w} G) (g : G) (m : M.obj.obj.V) :
    (M.obj.obj.ρ g⁻¹).asHom.hom ((M.obj.obj.ρ g).asHom.hom m) = m := by
  change ((M.obj.obj.ρ g).asHom ≫ (M.obj.obj.ρ g⁻¹).asHom).hom m = m
  rw [← End.mul_asHom, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- `g` undoes the action of `g⁻¹` on a discrete `G`-module. -/
lemma rho_apply_rho_inv_apply (M : ContinuousGAddCommGrp.{u, w} G) (g : G) (m : M.obj.obj.V) :
    (M.obj.obj.ρ g).asHom.hom ((M.obj.obj.ρ g⁻¹).asHom.hom m) = m := by
  simpa using rho_inv_apply_rho_apply M g⁻¹ m

/-- The identity element of `G` acts trivially on a discrete `G`-module. -/
private lemma rho_one_apply (M : ContinuousGAddCommGrp.{u, w} G) (m : M.obj.obj.V) :
    (M.obj.obj.ρ 1).asHom.hom m = m := by
  rw [map_one]
  rfl

variable (M N : ContinuousGAddCommGrp.{u, w} G)

/-- Conjugation by `g` on `Hom_ℤ(M, N)`: `φ ↦ g ∘ φ ∘ g⁻¹`. -/
def homConj (g : G) : (M.obj.obj.V →+ N.obj.obj.V) →+ (M.obj.obj.V →+ N.obj.obj.V) where
  toFun φ := (N.obj.obj.ρ g).asHom.hom.comp (φ.comp (M.obj.obj.ρ g⁻¹).asHom.hom)
  map_zero' := by ext; simp
  map_add' φ ψ := by ext; simp

/-- The value of `homConj M N g φ` at `m` is `g · φ(g⁻¹ · m)`. -/
lemma homConj_apply (g : G) (φ : M.obj.obj.V →+ N.obj.obj.V) (m : M.obj.obj.V) :
    homConj M N g φ m = (N.obj.obj.ρ g).asHom.hom (φ ((M.obj.obj.ρ g⁻¹).asHom.hom m)) :=
  rfl

/-- `Hom_ℤ(M, N)` with the conjugation action, as an action on an abelian group. -/
def homAction : Action AddCommGrpCat.{w} G where
  V := AddCommGrpCat.of (M.obj.obj.V →+ N.obj.obj.V)
  ρ :=
    { toFun g := End.of (AddCommGrpCat.ofHom (homConj M N g))
      map_one' := by
        apply End.ext
        apply AddCommGrpCat.hom_ext
        ext φ m
        change (N.obj.obj.ρ 1).asHom.hom (φ ((M.obj.obj.ρ 1⁻¹).asHom.hom m)) = φ m
        rw [inv_one, map_one, map_one]
        rfl
      map_mul' g h := by
        apply End.ext
        apply AddCommGrpCat.hom_ext
        ext φ m
        change (N.obj.obj.ρ (g * h)).asHom.hom (φ ((M.obj.obj.ρ (g * h)⁻¹).asHom.hom m)) =
          (N.obj.obj.ρ g).asHom.hom ((N.obj.obj.ρ h).asHom.hom
            (φ ((M.obj.obj.ρ h⁻¹).asHom.hom ((M.obj.obj.ρ g⁻¹).asHom.hom m))))
        rw [mul_inv_rev, map_mul, map_mul, End.mul_asHom, End.mul_asHom]
        rfl }

/-- The action of `g` on `φ` in `homAction M N` sends `m` to `g · φ(g⁻¹ · m)`. -/
lemma homAction_ρ_apply (g : G) (φ : M.obj.obj.V →+ N.obj.obj.V) (m : M.obj.obj.V) :
    (show M.obj.obj.V →+ N.obj.obj.V from ((homAction M N).ρ g).asHom.hom φ) m =
      (N.obj.obj.ρ g).asHom.hom (φ ((M.obj.obj.ρ g⁻¹).asHom.hom m)) :=
  rfl

/-- **The conjugation action on `Hom_ℤ(M, N)` is continuous for `M` finite.** The set of `g` with
`g · φ = ψ` contains, with any of its points `g₀`, the translate `g₀ O` of the open neighbourhood
`O` of `1` fixing the finitely many points of `M` and their images under `φ`. -/
theorem isContinuous_homAction [IsTopologicalGroup G] [Finite M.obj.obj.V] :
    (homAction M N).IsContinuous := by
  rw [Action.isContinuous_def]
  have : DiscreteTopology ((forget₂ (Action AddCommGrpCat G) TopCat).obj (homAction M N)) := ⟨rfl⟩
  have : DiscreteTopology ((forget₂ AddCommGrpCat TopCat).obj (homAction M N).V) := ⟨rfl⟩
  refine continuous_prod_of_discrete_right.mpr fun (φ : M.obj.obj.V →+ N.obj.obj.V) ↦
    continuous_discrete_rng.mpr fun (ψ : M.obj.obj.V →+ N.obj.obj.V) ↦ ?_
  change IsOpen {g : G | homConj M N g φ = ψ}
  rw [isOpen_iff_forall_mem_open]
  intro g₀ hg₀
  let O : Set G := ⋂ m : M.obj.obj.V,
    ({g | (M.obj.obj.ρ g).asHom.hom m = m} ∩ {g | (N.obj.obj.ρ g).asHom.hom (φ m) = φ m})
  have hO : IsOpen O := isOpen_iInter_of_finite fun m ↦
    (isOpen_setOf_rho_apply_eq M m).inter (isOpen_setOf_rho_apply_eq N (φ m))
  have h1 : (1 : G) ∈ O := Set.mem_iInter.mpr fun m ↦
    ⟨rho_one_apply M m, rho_one_apply N (φ m)⟩
  refine ⟨(g₀ * ·) '' O, ?_, isOpenMap_mul_left g₀ O hO, ⟨1, h1, mul_one g₀⟩⟩
  rintro _ ⟨o, ho, rfl⟩
  have ho' := Set.mem_iInter.mp ho
  change homConj M N (g₀ * o) φ = ψ
  have hfix : homConj M N o φ = φ := by
    ext m
    rw [homConj_apply]
    have hinv : (M.obj.obj.ρ o⁻¹).asHom.hom m = m := by
      conv_lhs => rw [← (ho' m).1]
      exact rho_inv_apply_rho_apply M o m
    rw [hinv]
    exact (ho' m).2
  have hmul : homConj M N (g₀ * o) φ = homConj M N g₀ (homConj M N o φ) :=
    congrArg (fun f : End (homAction M N).V ↦ f.asHom.hom φ)
      (map_mul (homAction M N).ρ g₀ o)
  rwa [hmul, hfix]

variable [IsTopologicalGroup G] [Finite M.obj.obj.V]

/-- **`Hom_ℤ(M, N)` as a discrete `G`-module**, `G` acting by conjugation, for `M` finite. -/
def hom : ContinuousGAddCommGrp.{u, w} G :=
  ⟨⟨homAction M N, isContinuous_homAction M N⟩, ⟨rfl⟩⟩

/-- The action of `g` on `φ` in `hom M N` sends `m` to `g · φ(g⁻¹ · m)`. -/
lemma hom_ρ_apply (g : G) (φ : M.obj.obj.V →+ N.obj.obj.V) (m : M.obj.obj.V) :
    (show M.obj.obj.V →+ N.obj.obj.V from ((hom M N).obj.obj.ρ g).asHom.hom φ) m =
      (N.obj.obj.ρ g).asHom.hom (φ ((M.obj.obj.ρ g⁻¹).asHom.hom m)) :=
  rfl

omit [IsTopologicalGroup G] [Finite M.obj.obj.V] in
/-- The underlying abelian group of a finite discrete `G`-module is finite. -/
instance finite_of_isFinite (M : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory) :
    Finite M.obj.obj.obj.V :=
  M.property

omit [Finite M.obj.obj.V] in
/-- `Hom_ℤ(M, N)` is finite when `M` and `N` are. -/
lemma finite_hom [Finite M.obj.obj.V] [Finite N.obj.obj.V] : Finite (hom M N).obj.obj.V :=
  show Finite (M.obj.obj.V →+ N.obj.obj.V) from
    Finite.of_injective (fun φ : M.obj.obj.V →+ N.obj.obj.V ↦ (φ : M.obj.obj.V → N.obj.obj.V))
      DFunLike.coe_injective

/-- **`Hom_ℤ(M, N)` of finite discrete `G`-modules**, as a finite discrete `G`-module. -/
def homIsFinite (M N : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory) :
    (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory :=
  haveI : Finite M.obj.obj.obj.V := M.property
  haveI : Finite N.obj.obj.obj.V := N.property
  ⟨hom M.obj N.obj, finite_hom M.obj N.obj⟩

/-! ### Morphisms into `Hom_ℤ(M, N)` are pairings -/

variable {M N}

/-- An element of `Hom_ℤ(M, N)`, read as an additive map. -/
def homOfElem (φ : ((forgetAction G).obj (hom M N)).obj.obj.V) : M.obj.obj.V →+ N.obj.obj.V := φ

/-- The additive map of `g · φ` sends `m` to `g · φ(g⁻¹ · m)`. -/
lemma homOfElem_rho (g : G) (φ : ((forgetAction G).obj (hom M N)).obj.obj.V)
    (m : M.obj.obj.V) :
    homOfElem (((forgetAction G).obj (hom M N)).obj.obj.ρ g φ) m =
      (N.obj.obj.ρ g).asHom.hom (homOfElem φ ((M.obj.obj.ρ g⁻¹).asHom.hom m)) :=
  rfl

variable (S : AlgebraicGeometry.ContinuousGSet.{u, w} G)

omit [IsTopologicalGroup G] in
/-- A morphism of continuous `G`-sets commutes with the actions, on elements. -/
lemma gsetHom_apply_rho {X : AlgebraicGeometry.ContinuousGSet.{u, w} G} (f : S ⟶ X) (g : G)
    (s : S.obj.obj.V) : f.hom.hom.hom (S.obj.obj.ρ g s) = X.obj.obj.ρ g (f.hom.hom.hom s) :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) s

omit [IsTopologicalGroup G] [Finite M.obj.obj.V] in
/-- A morphism of functors on the one-object category of `G` out of `S × M` commutes with the
actions, on elements. -/
lemma pairing_naturality_apply
    (β : (gsetPresheaf (G := G)).obj S ⊗ ((gmodulePresheaf (G := G)).obj M ⋙
        CategoryTheory.forget AddCommGrpCat) ⟶
      (gmodulePresheaf (G := G)).obj N ⋙ CategoryTheory.forget AddCommGrpCat)
    (g : G) (s : S.obj.obj.V) (m : M.obj.obj.V) :
    β.app (SingleObj.star G) (S.obj.obj.ρ g s, (M.obj.obj.ρ g).asHom.hom m) =
      (N.obj.obj.ρ g).asHom.hom (β.app (SingleObj.star G) (s, m)) :=
  ConcreteCategory.congr_hom (CC := fun X : Type w ↦ X)
    (β.naturality (X := SingleObj.star G) (Y := SingleObj.star G) g) (s, m)

/-- The pairing `S × M ⟶ N` of a morphism `S ⟶ Hom_ℤ(M, N)`, as a morphism of functors on the
one-object category of `G`. -/
def pairingOfGSetHom (f : S ⟶ (forgetAction G).obj (hom M N)) :
    (gsetPresheaf (G := G)).obj S ⊗ ((gmodulePresheaf (G := G)).obj M ⋙
        CategoryTheory.forget AddCommGrpCat) ⟶
      (gmodulePresheaf (G := G)).obj N ⋙ CategoryTheory.forget AddCommGrpCat where
  app _ := TypeCat.ofHom fun p ↦ homOfElem (f.hom.hom.hom p.1) p.2
  naturality _ _ g := by
    ext ⟨s, m⟩
    change homOfElem (f.hom.hom.hom (S.obj.obj.ρ g s)) ((M.obj.obj.ρ g).asHom.hom m) =
      (N.obj.obj.ρ g).asHom.hom (homOfElem (f.hom.hom.hom s) m)
    refine (congrArg (fun φ ↦ homOfElem φ ((M.obj.obj.ρ g).asHom.hom m))
      (gsetHom_apply_rho S f g s)).trans ?_
    refine (homOfElem_rho g (f.hom.hom.hom s) ((M.obj.obj.ρ g).asHom.hom m)).trans ?_
    rw [rho_inv_apply_rho_apply M g m]

/-- The pairing of `f` sends `(s, m)` to `f(s)(m)`. -/
lemma pairingOfGSetHom_app_apply (f : S ⟶ (forgetAction G).obj (hom M N)) (x : SingleObj G)
    (s : S.obj.obj.V) (m : M.obj.obj.V) :
    (pairingOfGSetHom S f).app x (s, m) = homOfElem (f.hom.hom.hom s) m :=
  rfl

/-- The morphism `S ⟶ Hom_ℤ(M, N)` of a pairing additive in its second variable. -/
def gsetHomOfPairing
    (β : (gsetPresheaf (G := G)).obj S ⊗ ((gmodulePresheaf (G := G)).obj M ⋙
        CategoryTheory.forget AddCommGrpCat) ⟶
      (gmodulePresheaf (G := G)).obj N ⋙ CategoryTheory.forget AddCommGrpCat)
    (hβ : Stacks.ConstantSheaf.IsAddRightPairing _ _ _ β) :
    S ⟶ (forgetAction G).obj (hom M N) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := TypeCat.ofHom fun s ↦ (AddMonoidHom.mk'
        (fun m : M.obj.obj.V ↦ β.app (SingleObj.star G) (s, m))
        (fun m m' ↦ hβ (SingleObj.star G) s m m') : M.obj.obj.V →+ N.obj.obj.V)
      comm := fun g ↦ by
        ext s
        refine AddMonoidHom.ext fun m ↦ ?_
        have h := pairing_naturality_apply S β g s ((M.obj.obj.ρ g⁻¹).asHom.hom m)
        rwa [rho_apply_rho_inv_apply M g m] at h })

variable (M N) in
/-- **Morphisms of continuous `G`-sets into `Hom_ℤ(M, N)` are the equivariant pairings
`S × M ⟶ N` additive in the second variable.** -/
def homPairingEquiv :
    (S ⟶ (forgetAction G).obj (hom M N)) ≃
      {β : (gsetPresheaf (G := G)).obj S ⊗ ((gmodulePresheaf (G := G)).obj M ⋙
          CategoryTheory.forget AddCommGrpCat) ⟶
          (gmodulePresheaf (G := G)).obj N ⋙ CategoryTheory.forget AddCommGrpCat //
        Stacks.ConstantSheaf.IsAddRightPairing _ _ _ β} where
  toFun f := ⟨pairingOfGSetHom S f, fun _ s m m' ↦ map_add (homOfElem (f.hom.hom.hom s)) m m'⟩
  invFun β := gsetHomOfPairing S β.1 β.2
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext s
    rfl
  right_inv β := by
    refine Subtype.ext ?_
    ext x ⟨s, m⟩
    rfl

/-- The bijection `homPairingEquiv` is natural in the `G`-set. -/
lemma pairingOfGSetHom_comp {S' : AlgebraicGeometry.ContinuousGSet.{u, w} G} (h : S' ⟶ S)
    (f : S ⟶ (forgetAction G).obj (hom M N)) :
    pairingOfGSetHom S' (h ≫ f) =
      (gsetPresheaf (G := G)).map h ▷ ((gmodulePresheaf (G := G)).obj M ⋙
        CategoryTheory.forget AddCommGrpCat) ≫ pairingOfGSetHom S f :=
  rfl

section Congr

omit [Finite M.obj.obj.V]

omit [IsTopologicalGroup G] in
/-- A morphism of discrete `G`-modules commutes with the actions, on elements. -/
lemma hom_apply_rho {P Q : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory} (f : P ⟶ Q)
    (g : G) (p : P.obj.obj.obj.V) :
    f.hom.hom.hom.hom.hom ((P.obj.obj.obj.ρ g).asHom.hom p) =
      (Q.obj.obj.obj.ρ g).asHom.hom (f.hom.hom.hom.hom.hom p) :=
  ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) p

/-- Morphisms between `Hom_ℤ(M, N)`'s of finite discrete `G`-modules are equal if they agree on
elements. -/
private lemma homIsFinite_hom_ext
    {M M' N N' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    {f f' : homIsFinite M N ⟶ homIsFinite M' N'}
    (h : ∀ (φ : M.obj.obj.obj.V →+ N.obj.obj.obj.V) (m : M'.obj.obj.obj.V),
      (show M'.obj.obj.obj.V →+ N'.obj.obj.obj.V from f.hom.hom.hom.hom.hom φ) m =
        (show M'.obj.obj.obj.V →+ N'.obj.obj.obj.V from f'.hom.hom.hom.hom.hom φ) m) :
    f = f' := by
  iterate 3 apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ AddMonoidHom.ext (h φ))

/-- Conjugating additive maps by morphisms of finite discrete `G`-modules, `φ ↦ b ∘ φ ∘ a`. -/
def homIsFiniteMap {M M' N N' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    (a : M' ⟶ M) (b : N ⟶ N') : homIsFinite M N ⟶ homIsFinite M' N' :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun φ : M.obj.obj.obj.V →+ N.obj.obj.obj.V ↦
            b.hom.hom.hom.hom.hom.comp (φ.comp a.hom.hom.hom.hom.hom)
          map_zero' := by ext; simp
          map_add' := fun φ ψ ↦ by ext; simp }
      comm := fun g ↦ by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
          fun (φ : M.obj.obj.obj.V →+ N.obj.obj.obj.V) ↦ AddMonoidHom.ext fun m ↦ ?_)
        change b.hom.hom.hom.hom.hom ((N.obj.obj.obj.ρ g).asHom.hom (φ ((M.obj.obj.obj.ρ g⁻¹).asHom.hom
            (a.hom.hom.hom.hom.hom m)))) =
          (N'.obj.obj.obj.ρ g).asHom.hom (b.hom.hom.hom.hom.hom (φ (a.hom.hom.hom.hom.hom
            ((M'.obj.obj.obj.ρ g⁻¹).asHom.hom m))))
        rw [hom_apply_rho b g, ← hom_apply_rho a g⁻¹] }))

/-- The map `homIsFiniteMap a b` sends `φ` to `b ∘ φ ∘ a`. -/
lemma homIsFiniteMap_apply {M M' N N' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    (a : M' ⟶ M) (b : N ⟶ N') (φ : M.obj.obj.obj.V →+ N.obj.obj.obj.V) (m : M'.obj.obj.obj.V) :
    (show M'.obj.obj.obj.V →+ N'.obj.obj.obj.V from
      (homIsFiniteMap a b).hom.hom.hom.hom.hom φ) m =
      b.hom.hom.hom.hom.hom (φ (a.hom.hom.hom.hom.hom m)) :=
  rfl

/-- **`Hom_ℤ(-, -)` of finite discrete `G`-modules along isomorphisms.** -/
def homIsFiniteCongr {M M' N N' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    (a : M ≅ M') (b : N ≅ N') : homIsFinite M N ≅ homIsFinite M' N' where
  hom := homIsFiniteMap a.inv b.hom
  inv := homIsFiniteMap a.hom b.inv
  hom_inv_id := by
    iterate 3 apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
      fun (φ : M.obj.obj.obj.V →+ N.obj.obj.obj.V) ↦ AddMonoidHom.ext fun m ↦ ?_)
    change (a.hom ≫ a.inv).hom.hom.hom.hom.hom m |> fun m' ↦ (b.hom ≫ b.inv).hom.hom.hom.hom.hom
      (φ m') = φ m
    rw [a.hom_inv_id, b.hom_inv_id]
    rfl
  inv_hom_id := by
    iterate 3 apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
      fun (φ : M'.obj.obj.obj.V →+ N'.obj.obj.obj.V) ↦ AddMonoidHom.ext fun m ↦ ?_)
    change (a.inv ≫ a.hom).hom.hom.hom.hom.hom m |> fun m' ↦ (b.inv ≫ b.hom).hom.hom.hom.hom.hom
      (φ m') = φ m
    rw [a.inv_hom_id, b.inv_hom_id]
    rfl

/-- `homIsFiniteMap` sends a pair of identities to the identity. -/
lemma homIsFiniteMap_id (M N : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory) :
    homIsFiniteMap (𝟙 M) (𝟙 N) = 𝟙 (homIsFinite M N) := by
  exact homIsFinite_hom_ext fun _ _ ↦ rfl

/-- `homIsFiniteMap` is compatible with composition:
`homIsFiniteMap a b ≫ homIsFiniteMap a' b' = homIsFiniteMap (a' ≫ a) (b ≫ b')`. -/
lemma homIsFiniteMap_comp
    {M M' M'' N N' N'' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    (a : M' ⟶ M) (b : N ⟶ N') (a' : M'' ⟶ M') (b' : N' ⟶ N'') :
    homIsFiniteMap a b ≫ homIsFiniteMap a' b' = homIsFiniteMap (a' ≫ a) (b ≫ b') := by
  exact homIsFinite_hom_ext fun _ _ ↦ rfl

/-- **`homIsFiniteCongr` is natural in the first variable.** -/
lemma homIsFiniteMap_comp_homIsFiniteCongr
    {M M' M₁ M₁' N N' : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}
    (a : M ≅ M₁) (a' : M' ≅ M₁') (b : N ≅ N') (v : M' ⟶ M) (v₁ : M₁' ⟶ M₁)
    (hv : v ≫ a.hom = a'.hom ≫ v₁) :
    homIsFiniteMap v (𝟙 N) ≫ (homIsFiniteCongr a' b).hom =
      (homIsFiniteCongr a b).hom ≫ homIsFiniteMap v₁ (𝟙 N') := by
  have hv' : a'.inv ≫ v = v₁ ≫ a.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hv, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  change homIsFiniteMap v (𝟙 N) ≫ homIsFiniteMap a'.inv b.hom =
    homIsFiniteMap a.inv b.hom ≫ homIsFiniteMap v₁ (𝟙 N')
  rw [homIsFiniteMap_comp, homIsFiniteMap_comp, hv', Category.id_comp, Category.comp_id]

end Congr

section IsoOfForget

omit [IsTopologicalGroup G] [Finite M.obj.obj.V]

variable {M N : (ContinuousGAddCommGrp.isFinite.{u, w} G).FullSubcategory}

/-- The bijection of underlying sets of an isomorphism of the underlying finite `G`-sets of two
finite discrete `G`-modules. -/
def forgetActionIsFiniteIsoEquiv
    (φ : (forgetActionIsFinite G).obj M ≅ (forgetActionIsFinite G).obj N) :
    M.obj.obj.obj.V ≃ N.obj.obj.obj.V where
  toFun x := φ.hom.hom.hom.hom.hom x
  invFun y := φ.inv.hom.hom.hom.hom y
  left_inv x := by
    change (φ.hom ≫ φ.inv).hom.hom.hom.hom.hom x = x
    rw [φ.hom_inv_id]
    rfl
  right_inv y := by
    change (φ.inv ≫ φ.hom).hom.hom.hom.hom.hom y = y
    rw [φ.inv_hom_id]
    rfl

/-- **An isomorphism of the underlying finite `G`-sets which is additive is an isomorphism of
finite discrete `G`-modules.** -/
noncomputable def isoOfForgetActionIsFiniteIso
    (φ : (forgetActionIsFinite G).obj M ≅ (forgetActionIsFinite G).obj N)
    (hφ : ∀ x y : M.obj.obj.obj.V, forgetActionIsFiniteIsoEquiv φ (x + y) =
      forgetActionIsFiniteIsoEquiv φ x + forgetActionIsFiniteIsoEquiv φ y) : M ≅ N :=
  let a : M.obj.obj.obj.V ≃+ N.obj.obj.obj.V := AddEquiv.mk' (forgetActionIsFiniteIsoEquiv φ) hφ
  { hom := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      { hom := AddCommGrpCat.ofHom a.toAddMonoidHom
        comm := fun g ↦ by
          ext x
          exact ConcreteCategory.congr_hom (φ.hom.hom.hom.hom.comm g) x }))
    inv := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      { hom := AddCommGrpCat.ofHom a.symm.toAddMonoidHom
        comm := fun g ↦ by
          ext x
          exact ConcreteCategory.congr_hom (φ.inv.hom.hom.hom.comm g) x }))
    hom_inv_id := by
      iterate 3 apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      ext x
      exact a.symm_apply_apply x
    inv_hom_id := by
      iterate 3 apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      ext x
      exact a.apply_symm_apply x }

/-- The forward map of `isoOfForgetActionIsFiniteIso φ hφ` is the underlying map of `φ`. -/
lemma isoOfForgetActionIsFiniteIso_hom_apply
    (φ : (forgetActionIsFinite G).obj M ≅ (forgetActionIsFinite G).obj N)
    (hφ : ∀ x y : M.obj.obj.obj.V, forgetActionIsFiniteIsoEquiv φ (x + y) =
      forgetActionIsFiniteIsoEquiv φ x + forgetActionIsFiniteIsoEquiv φ y) (x : M.obj.obj.obj.V) :
    (isoOfForgetActionIsFiniteIso φ hφ).hom.hom.hom.hom.hom x = forgetActionIsFiniteIsoEquiv φ x :=
  rfl

end IsoOfForget

end ContinuousGAddCommGrp

end CategoryTheory

end
