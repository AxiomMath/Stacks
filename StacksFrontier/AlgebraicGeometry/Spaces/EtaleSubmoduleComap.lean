module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGerms

/-!
# The right adjoint of restricting a submodule along an étale morphism

Let `g : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` and `M` an
`𝒪_X`-module.  Restriction of submodules along `g` has a right adjoint: the submodule of `M`
whose sections over a chart `T` of `X` are those restricting into a given submodule of `M|_Y`
along every chart morphism `g ∘ V ⟶ T`.  Consequently restriction preserves least upper bounds.

## Main definitions

* `AlgebraicGeometry.Space.etaleSubmoduleComap`: the right adjoint.

## Main results

* `AlgebraicGeometry.Space.le_etaleSubmoduleComap_iff`: the adjunction.
* `AlgebraicGeometry.Space.etaleSubmoduleRestrict_sup`: restriction preserves binary suprema.
* `AlgebraicGeometry.Space.le_of_forall_etaleGermSet_subset`: germ-set containment at every
  lift of every geometric point gives containment of submodules.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **The right adjoint of restriction along an étale morphism.**  The sections of `M` over a
chart `T` of `X` whose restriction along every chart morphism `g ∘ V ⟶ T` lies in `K`. -/
def etaleSubmoduleComap (K : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule) :
    M.Submodule :=
  etaleSubmoduleGlue B S hS (fun _ : PUnit.{u + 1} => Y) (fun _ => g) (fun _ => hg) fun _ => K

/-- A section of `M` over a chart `T` of `X` lies in `etaleSubmoduleComap B S hS g hg K` exactly
when its restriction along every chart morphism `g ∘ V ⟶ T` lies in `K`. -/
theorem mem_etaleSubmoduleComap_obj
    (K : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    (T : (smallEtaleRingedSite B S hS X.1 X.2).C) (s : M.val.obj (op T)) :
    s ∈ (etaleSubmoduleComap B S hS g hg K).obj (op T) ↔
      ∀ (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
        (φ : (ringedSitePostcomp B S hS g hg).obj V ⟶ T),
        M.val.map φ.op s ∈ K.obj (op V) := by
  rw [etaleSubmoduleComap, mem_etaleSubmoduleGlue_obj]
  exact ⟨fun hs V φ => hs PUnit.unit V φ, fun hs _ V φ => hs V φ⟩

/-- **The adjunction**: a submodule of `M` restricts into `K` exactly when it is contained in
the comap of `K`. -/
theorem le_etaleSubmoduleComap_iff (N : M.Submodule)
    (K : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule) :
    N ≤ etaleSubmoduleComap B S hS g hg K ↔ etaleSubmoduleRestrict B S hS g hg N ≤ K := by
  constructor
  · intro h V s hs
    have := (mem_etaleSubmoduleComap_obj B S hS g hg K ((ringedSitePostcomp B S hS g hg).obj V.unop)
      s).1 (h (op ((ringedSitePostcomp B S hS g hg).obj V.unop)) hs) V.unop (𝟙 _)
    simp only [op_id, PresheafOfModules.map_id] at this
    exact this
  · intro h T s hs
    exact (mem_etaleSubmoduleComap_obj B S hS g hg K T.unop s).2 fun V φ ↦
      h (op V) (N.map_mem φ.op hs)

/-- Restriction along an étale morphism is monotone. -/
theorem etaleSubmoduleRestrict_mono {N N' : M.Submodule} (h : N ≤ N') :
    etaleSubmoduleRestrict B S hS g hg N ≤ etaleSubmoduleRestrict B S hS g hg N' := by
  intro V s hs
  exact h (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) hs

/-- **Restriction along an étale morphism preserves binary suprema.** -/
theorem etaleSubmoduleRestrict_sup (N N' : M.Submodule) :
    etaleSubmoduleRestrict B S hS g hg (N ⊔ N') =
      etaleSubmoduleRestrict B S hS g hg N ⊔ etaleSubmoduleRestrict B S hS g hg N' := by
  refine le_antisymm ?_ (sup_le (etaleSubmoduleRestrict_mono B S hS g hg le_sup_left)
    (etaleSubmoduleRestrict_mono B S hS g hg le_sup_right))
  rw [← le_etaleSubmoduleComap_iff]
  exact sup_le ((le_etaleSubmoduleComap_iff B S hS g hg N _).2 le_sup_left)
    ((le_etaleSubmoduleComap_iff B S hS g hg N' _).2 le_sup_right)

/-- A supremum whose first summand restricts into the second restricts to the second. -/
theorem etaleSubmoduleRestrict_sup_eq_right (N N' : M.Submodule)
    (h : etaleSubmoduleRestrict B S hS g hg N ≤ etaleSubmoduleRestrict B S hS g hg N') :
    etaleSubmoduleRestrict B S hS g hg (N ⊔ N') = etaleSubmoduleRestrict B S hS g hg N' :=
  (etaleSubmoduleRestrict_sup B S hS g hg N N').trans (sup_eq_right.2 h)

/-- Germ sets are monotone in the submodule. -/
theorem etaleGermSet_mono {N N' : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule}
    (h : N ≤ N') {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x) :
    etaleGermSet B S hS g hg N t ⊆ etaleGermSet B S hS g hg N' t := by
  rintro e ⟨V, w, n, hn, rfl⟩
  exact ⟨V, w, n, h (op V) hn, rfl⟩

/-- **Containment of submodules of `M|_Y` from containment of germ sets** at every lift of
every geometric point of `X`. -/
theorem le_of_forall_etaleGermSet_subset
    {N N' : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule}
    (h : ∀ (x : GeometricPoint B S hS X.1) (t : GeometricPointLift B S hS g.hom x),
      etaleGermSet B S hS g hg N t ⊆ etaleGermSet B S hS g hg N' t) :
    N ≤ N' := by
  intro V s hs
  exact mem_of_forall_germ_mem_etaleGermSet B S hS g hg N' V.unop s fun x t w =>
    h x t (germ_mem_etaleGermSet B S hS g hg N t V.unop w s hs)

end AlgebraicGeometry.Space

end
