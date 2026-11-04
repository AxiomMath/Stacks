module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTor

/-!
# The terms of the twist complex of an injective resolution are acyclic

Let `Y` be a scheme and `Λ` a ring, not necessarily commutative. For a finite free right
`Λ`-module `N` with a basis indexed by `ι` and an injective sheaf of `Λ`-modules `J`, the twist
`N ⊗[Λ] J` is the underlying abelian sheaf of the sheaf of `Λ`-modules `U ↦ (ι → J(U))`, which is
injective; so it is acyclic for sheaf cohomology by Tag 03FD. A total degree of the twist complex
of an injective resolution by a complex of finite free modules with finitely many nonzero terms is
a coproduct of finitely many such twists, hence acyclic as well. This is the acyclicity input of
the dimension shifting in the proof of [Stacks, Tag 03TV].

## Main definitions

* `Stacks.SheafTwist.powModule`: the functor `M ↦ (ι → M)` on left `Λ`-modules.

## Main results

* `Stacks.SheafTwist.injective_powSheaf`: `U ↦ (ι → J(U))` is injective when `J` is.
* `Stacks.SheafTwist.subsingleton_ext_twist`: twists of injectives are acyclic.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Abelian
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe w u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ]

/-- The functor `M ↦ (ι → M)` on left `Λ`-modules. -/
def powModule (ι : Type (max (u + 1) r)) :
    ModuleCat.{max (u + 1) r} Λ ⥤ ModuleCat.{max (u + 1) r} Λ where
  obj M := ModuleCat.of Λ (ι → M)
  map f := ModuleCat.ofHom (LinearMap.pi fun i => f.hom.comp (LinearMap.proj i))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (Y : Scheme.{u}) (ι : Type (max (u + 1) r))

/-- The functor `M ↦ (ι → M)` preserves limits. -/
instance preservesLimitsOfSize_powModule :
    PreservesLimitsOfSize.{u, u + 1} (powModule.{u, r} (Λ := Λ) ι) := by
  have e : powModule.{u, r} (Λ := Λ) ι ⋙ forget (ModuleCat.{max (u + 1) r} Λ) ≅
      forget (ModuleCat.{max (u + 1) r} Λ) ⋙ coyoneda.obj (op ι) :=
    NatIso.ofComponents (fun M => (TypeCat.homEquiv (X := ι) (Y := M)).symm.toIso) (fun f => by
      ext x
      rfl)
  have : PreservesLimits (powModule.{u, r} (Λ := Λ) ι ⋙
      forget (ModuleCat.{max (u + 1) r} Λ)) := preservesLimits_of_natIso e.symm
  have : PreservesLimits (powModule.{u, r} (Λ := Λ) ι) :=
    preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{max (u + 1) r} Λ))
  exact preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _

/-- Composing with `M ↦ (ι → M)` takes étale sheaves of `Λ`-modules to sheaves. -/
instance hasSheafCompose_powModule :
    Y.smallEtaleTopology.HasSheafCompose (powModule.{u, r} (Λ := Λ) ι) :=
  hasSheafCompose_of_preservesLimitsOfSize _

/-- The sheaf `U ↦ (ι → J(U))`. -/
abbrev powSheaf (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y :=
  (sheafCompose Y.smallEtaleTopology (powModule.{u, r} (Λ := Λ) ι)).obj J

/-- The projection `(ι → J) ⟶ J` onto a coordinate. -/
def powSheafProj (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) (i : ι) :
    powSheaf Y ι J ⟶ J :=
  ⟨{ app := fun U => ModuleCat.ofHom (LinearMap.proj i)
     naturality := fun _ _ _ => rfl }⟩

/-- The morphism into `(ι → J)` assembled from its coordinates. -/
def powSheafLift {A J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y} (φ : ι → (A ⟶ J)) :
    A ⟶ powSheaf Y ι J :=
  ⟨{ app := fun U => ModuleCat.ofHom (LinearMap.pi fun i => ((φ i).hom.app U).hom)
     naturality := fun U V g => by
       ext x
       funext i
       exact ConcreteCategory.congr_hom ((φ i).hom.naturality g) x }⟩

/-- The coordinates of `powSheafLift Y ι φ` are the morphisms `φ i`. -/
@[reassoc (attr := simp)]
lemma powSheafLift_proj {A J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y}
    (φ : ι → (A ⟶ J)) (i : ι) : powSheafLift Y ι φ ≫ powSheafProj Y ι J i = φ i :=
  rfl

/-- Two morphisms into `U ↦ (ι → J(U))` with the same coordinates are equal. -/
lemma powSheaf_hom_ext {A J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y}
    (f g : A ⟶ powSheaf Y ι J) (h : ∀ i, f ≫ powSheafProj Y ι J i = g ≫ powSheafProj Y ι J i) :
    f = g := by
  apply Sheaf.hom_ext
  ext U x
  funext i
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) (h i)) x

/-- **`U ↦ (ι → J(U))` is injective when `J` is.** -/
instance injective_powSheaf (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) [Injective J] :
    Injective (powSheaf Y ι J) where
  factors {A B} f m _ :=
    ⟨powSheafLift Y ι (fun i => Injective.factorThru (f ≫ powSheafProj Y ι J i) m),
      powSheaf_hom_ext Y ι _ _ fun i => by simp⟩

/-! ### Twists of injectives -/

section Twist

variable (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)

/-- Tensoring with a right module with a finite basis is, after forgetting to abelian groups, the
`ι`-th power of left modules. -/
def tensorAbIso {N : ModuleCat.{max (u + 1) r} (MulOpposite Λ)} [Fintype ι]
    (b : Module.Basis ι (MulOpposite Λ) N) :
    tensorAb D N ≅ powModule.{u, r} (Λ := Λ) ι ⋙ Stacks.EtaleResolution.forgetAb.{u + 1} Λ :=
  Functor.isoWhiskerRight (tensorBasisRightIso D b) (forget₂ (ModuleCat ℤ) AddCommGrpCat) ≪≫
    NatIso.ofComponents (fun M => Iso.refl _) (fun f => rfl)

/-- An isomorphism of coefficient functors induces an isomorphism of the composed sheaves. -/
def sheafComposeIso {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    [Y.smallEtaleTopology.HasSheafCompose F] [Y.smallEtaleTopology.HasSheafCompose G] (e : F ≅ G) :
    sheafCompose Y.smallEtaleTopology F ≅ sheafCompose Y.smallEtaleTopology G where
  hom := sheafCompose_map Y.smallEtaleTopology e.hom
  inv := sheafCompose_map Y.smallEtaleTopology e.inv
  hom_inv_id := by rw [← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]
  inv_hom_id := by rw [← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]

/-- Composing with `M ↦ (ι → M)` followed by the forgetful functor to abelian groups takes étale
sheaves of `Λ`-modules to sheaves. -/
instance hasSheafCompose_powModule_forgetAb :
    Y.smallEtaleTopology.HasSheafCompose
      (powModule.{u, r} (Λ := Λ) ι ⋙ Stacks.EtaleResolution.forgetAb.{u + 1} Λ) := by
  have : PreservesLimitsOfSize.{u, u + 1} (Stacks.EtaleResolution.forgetAb.{u + 1} Λ) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  exact hasSheafCompose_of_preservesLimitsOfSize _

/-- **The twist of a sheaf by a right module with a finite basis is the underlying abelian sheaf
of a power.** -/
def twistIsoForgetPow (N : FiniteFree.{max (u + 1) r} Λ) [Fintype ι]
    (b : Module.Basis ι (MulOpposite Λ) N.obj)
    (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    ((twist.{u, r} D Y).obj N).obj J ≅
      (Stacks.EtaleResolution.sheafForget Λ Y).obj (powSheaf Y ι J) :=
  (sheafComposeIso Y (tensorAbIso.{u, r} ι D b)).app J

variable [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})]

/-- Acyclicity transports along an isomorphism. -/
lemma subsingleton_ext_of_iso {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {X A B : C}
    (e : A ≅ B) (n : ℕ) (h : Subsingleton (Ext.{w} X A n)) : Subsingleton (Ext.{w} X B n) :=
  (Stacks.EtaleResolution.injective_comp_mk₀_hom e.symm n).subsingleton

/-- **The twist of an injective sheaf of `Λ`-modules by a finite free right module is acyclic.** -/
lemma subsingleton_ext_twist (N : FiniteFree.{max (u + 1) r} Λ)
    (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) [Injective J] (q : ℕ) :
    Subsingleton (Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y) (((twist.{u, r} D Y).obj N).obj J)
      (q + 1)) :=
  subsingleton_ext_of_iso
    (twistIsoForgetPow Y _ D N (Module.Free.chooseBasis (MulOpposite Λ) N.obj) J).symm (q + 1)
    (Stacks.InjectiveAcyclic.subsingleton_H_forget₂.{u, u + 1, u + 1, r, w}
      Y.smallEtaleTopology Λ (powSheaf Y _ J) q)

/-- **The terms of the twist complex of a complex of injective sheaves are acyclic**, when the
complex of finite free modules has finitely many nonzero terms. -/
lemma subsingleton_ext_twistComplex_X (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    [∀ n, Injective (I.X n)] (e c : ℤ) (h : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    [HomologicalComplex.HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)]
    (n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y) ((twistComplex D Y R I).X n)
      (q + 1)) := by
  let K := ((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R |>.obj I
  have hK := finite_support_of_columnBounds K e c (fun p hp =>
    isZero_of_forall_isZero_X fun q => ((twist.{u, r} D Y).map_isZero (h p hp)).obj (I.X q)) n
  let S : Set ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n}) := {j | ¬ IsZero (K.toGradedObject j.1)}
  have : Finite ↥S :=
    ((hK.preimage Subtype.val_injective.injOn).subset fun j hj => ⟨j.2, hj⟩).to_subtype
  let G := extFunctorObj (Stacks.EtaleSections.zSheaf.{r} Y) (q + 1)
  have hc := StacksDraft.TotalComplexQuasiIso.isColimitMapCofan _
    (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n) S
    (fun _ hj => not_not.1 hj) G
  have hz := StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _ hc (fun j => by
    show IsZero (AddCommGrpCat.of (Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y)
      (((twist.{u, r} D Y).obj (R.X j.1.1)).obj (I.X j.1.2)) (q + 1)))
    have := subsingleton_ext_twist.{w} Y D (R.X j.1.1) (I.X j.1.2) q
    exact AddCommGrpCat.isZero_of_subsingleton _)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hz

end Twist

end Stacks.SheafTwist

end
