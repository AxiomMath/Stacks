module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FiniteLevelStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteLocallyConstantAbelian

/-!
# The levels of a lisse ℓ-adic sheaf are finite locally constant

An ℓ-adic sheaf `F = {Fₙ}` is lisse when every `Fₙ` is locally constant
([Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)). Since the stalks of `Fₙ` are finite
(Tag 03UQ), the local values are finite, so every `Fₙ` is a *finite* locally constant sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules: over a member `V` of a trivialising covering which has a point, a geometric
point of `X` lifts to `V` and the stalk there is the local value; the members without points are
superfluous, being covered by the empty sieve.

The levels of the torsion-free model `ℓᴺ F` of a lisse `F` are again finite locally constant: the
underlying abelian sheaf of each is the image of an endomorphism of a finite locally constant
abelian sheaf, and these form a weak Serre subcategory (Tag 093U (2)).

## Main results

* `LAdicSheaf.isFiniteLocallyConstant_level_of_isLisse`: the levels of a lisse ℓ-adic sheaf are
  finite locally constant.
* `LAdicSheaf.isFiniteLocallyConstant_underlyingLAdicLevel_of_isLisse`: so are their underlying
  abelian sheaves.
* `LAdicSheaf.isFiniteLocallyConstant_underlyingLAdicLevel_torsionFreeModel`: so are those of the
  torsion-free model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

/-- **The levels of a lisse ℓ-adic sheaf are finite locally constant**: the local values of a
locally constant level are its stalks at geometric points lifting to the trivialising members,
which are finite (Tag 03UQ); members without points are dropped, being covered by the empty
sieve. -/
public theorem isFiniteLocallyConstant_level_of_isLisse (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hF : F.IsLisse) (n : ℕ) :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property) (F.level n) := by
  have : ∀ Y : SmallEtale B X.1 X.property,
      ((SmallEtale.topology B X.1 X.property).over Y).WEqualsLocallyBijective
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun Y =>
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, 0, 0} _ _
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))) := by
    rw [← HasForget₂.forget_comp (C := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (D := AddCommGrpCat.{u + 1})]
    infer_instance
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hcov, hconst⟩ := (hF n).exists_cover U
  let I' := {i : I // Nonempty ((SmallEtale.toScheme B X.1 X.property).obj (V i))}
  refine ⟨I', fun i => V i.1, fun i => f i.1, ?_, fun i => ?_⟩
  · refine (SmallEtale.topology B X.1 X.property).transitive hcov _ fun W g hg => ?_
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
    by_cases hi : Nonempty ((SmallEtale.toScheme B X.1 X.property).obj (V i))
    · have hmem : (Sieve.ofArrows (fun j : I' => V j.1) (fun j => f j.1)).arrows (a ≫ f i) :=
        (Sieve.mem_ofArrows_iff (fun j : I' => V j.1) (fun j => f j.1) (a ≫ f i)).2
          ⟨⟨i, hi⟩, a, rfl⟩
      rw [Sieve.pullback_eq_top_of_mem _ hmem]
      exact (SmallEtale.topology B X.1 X.property).top_mem W
    · have hW : IsEmpty ((SmallEtale.toScheme B X.1 X.property).obj W) :=
        ⟨fun w => hi ⟨((SmallEtale.toScheme B X.1 X.property).map a).base w⟩⟩
      exact (SmallEtale.topology B X.1 X.property).superset_covering bot_le
        (bot_mem_topology B X.property hW)
  · obtain ⟨E, ⟨e⟩⟩ := (hconst i.1).mem_essImage
    obtain ⟨v⟩ := i.2
    let t : GeometricPoint X.1 :=
      (GeometricPoint.ofPoint ((SmallEtale.toScheme B X.1 X.property).obj (V i.1)) v).map
        (B.inclusion.map (V i.1).obj.hom)
    let y : (geometricPointFiber B X.1 X.property t).obj (V i.1) :=
      ⟨(GeometricPoint.ofPoint _ v).hom, rfl⟩
    exact ⟨E, @Finite.of_equiv _ _ (finite_finiteLevelStalk B X ℓ F t n)
      (sheafFiberIsoOfConstantOver (geometricPointSitePoint B X.1 X.property t) y
        (F.level n) E e).toLinearEquiv.toEquiv, ⟨e⟩⟩

/-- The underlying abelian sheaves of the levels of a lisse ℓ-adic sheaf are finite locally
constant. -/
public theorem isFiniteLocallyConstant_underlyingLAdicLevel_of_isLisse
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF : F.IsLisse) (n : ℕ) :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property)
      (underlyingLAdicLevel B X ℓ F n) :=
  (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ _ _ _).1
    (isFiniteLocallyConstant_level_of_isLisse F hF n)

/-- **The levels of the torsion-free model of a lisse ℓ-adic sheaf are finite locally
constant**, on underlying abelian sheaves: `ℓᴺ F_{N+n}` is the image of the endomorphism `ℓᴺ` of
the finite locally constant sheaf `F_{N+n}`, the kernel of the projection onto its cokernel. -/
public theorem isFiniteLocallyConstant_underlyingLAdicLevel_torsionFreeModel
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF : F.IsLisse) (N n : ℕ) :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.property)
      (underlyingLAdicLevel B X ℓ (torsionFreeModel F N) n) := by
  let P := isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
    (SmallEtale.topology B X.1 X.property)
  have : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf B X.1 X.property
  have h : P (underlyingLAdicLevel B X ℓ F (N + n)) :=
    isFiniteLocallyConstant_underlyingLAdicLevel_of_isLisse F hF (N + n)
  have hc : P (cokernel ((ℓ ^ N) • 𝟙 (underlyingLAdicLevel B X ℓ F (N + n)))) :=
    P.prop_cokernel _ h h
  exact P.prop_of_iso (torsionFreeModelLevelIso F N n).symm (P.prop_kernel _ h hc)

end LAdicSheaf

end Stacks.EtaleCohomology

end
