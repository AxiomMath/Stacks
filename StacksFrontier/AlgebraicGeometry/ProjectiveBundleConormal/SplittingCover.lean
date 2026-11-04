module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.AffineBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The cover on which an invertible quotient splits

Let `X` be a scheme, `ℰ` a sheaf of `𝒪_X`-modules and `q : ℰ ⟶ 𝓛` an invertible quotient of
`ℰ`, that is, an epimorphism onto an invertible module. Around every point of `X` there is an
affine open `U` on which `𝓛` is trivial and on which some section of `ℰ` maps to a generator of
`𝓛`. No quasi-coherence of `ℰ` is needed.

## Main results

* `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting`: **the cover on which the
  quotient splits**, with both the sheaf-level trivialization `𝓛.restrict U.ι ≅ 𝒪_U` and a
  section-level trivialization `e : Γ(𝓛, U) ≃ₗ[Γ(X, U)] Γ(X, U)` carrying the image of the
  section to `1`.
* `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting_span`: the same with the
  generator named and the trivializations forgotten, so that generation is the statement that
  the generator spans `Γ(𝓛, U)`.

## Implementation notes

The generator and the section of `ℰ` lifting it live on different opens: the generator on a
trivializing open `V`, the lift on some `W ⊆ V`, and the affine open `U` returned is smaller than
both. The trivialization on `U` is therefore obtained from the one on `V`: it is read as
`𝓛.over V ≅ 𝒪|_V` on the slice `Over V` (`Stacks.Modules.overIsoUnitOfRestrictIsoUnit`), its
inverse is a section `σ` of `𝓛.over V` (`SheafOfModules.unitHomEquiv`), and the trivialization on
`U` is that isomorphism evaluated at the object `U ⟶ V` of `Over V`, so that it carries the
component of `σ` at `U` to `1`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} {E : X.Modules}

/-- **The cover on which the quotient splits.** Around every point of `X` there is an affine
open `U` on which `Q.L` is trivial and on which some section of `E` maps to a generator of
`Q.L`: both the sheaf-level trivialization `Q.L.restrict U.ι ≅ 𝒪_U` and a section-level frame
`e : Γ(Q.L, U) ≃ₗ Γ(X, U)` are produced, and `e` carries the image of the section to `1`. -/
theorem exists_affine_open_splitting (Q : Stacks.Divisors.InvertibleQuotient X E) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (Q.L.restrict U.ι ≅ _root_.SheafOfModules.unit (↑U : Scheme.{u}).ringCatSheaf) ∧
        ∃ (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (s : Γ(E, U)), e (Q.q.app U s) = 1 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  have : Epi (C := _root_.SheafOfModules.{u} X.ringCatSheaf) Q.q := Q.epi
  obtain ⟨V, -, hxV, -, ⟨eV⟩⟩ :=
    Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible Q.L (W := ⊤) (x := x)
      trivial
  let eV' : _root_.SheafOfModules.over Q.L V ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over V) :=
    Stacks.Modules.overIsoUnitOfRestrictIsoUnit Q.L V eV
  let σ : (_root_.SheafOfModules.over Q.L V).sections :=
    (_root_.SheafOfModules.over Q.L V).unitHomEquiv eV'.inv
  obtain ⟨W, f, ⟨s₀, hs₀⟩, hxW⟩ :=
    Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi (R := X.ringCatSheaf) (M := E)
      (N := Q.L) Q.q (V := V) (σ.val (op (Over.mk (𝟙 V)))) x hxV
  obtain ⟨U, hU, hxU, hUW, ⟨eU⟩⟩ :=
    Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible Q.L (W := W) hxW
  have hUV : U ≤ V := hUW.trans (leOfHom f)
  have hs : Q.q.app W (show Γ(E, W) from s₀)
      = Q.L.presheaf.map f.op (σ.val (op (Over.mk (𝟙 V)))) := hs₀
  refine ⟨U, hxU, hU, ⟨eU⟩,
    ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over V)
      (op (Over.mk (homOfLE hUV)))).mapIso eV').toLinearEquiv,
    E.presheaf.map (homOfLE hUW).op (show Γ(E, W) from s₀), ?_⟩
  have h₁ : Q.q.app U (E.presheaf.map (homOfLE hUW).op (show Γ(E, W) from s₀))
      = Q.L.presheaf.map (homOfLE hUW).op (Q.q.app W (show Γ(E, W) from s₀)) :=
    NatTrans.naturality_apply Q.q.mapPresheaf (homOfLE hUW).op _
  have h₂ : Q.L.presheaf.map f.op (σ.val (op (Over.mk (𝟙 V))))
      = (σ.val (op (Over.mk f)) : Γ(Q.L, W)) :=
    σ.property (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 V)).op
  have h₃ : Q.L.presheaf.map (homOfLE hUW).op (σ.val (op (Over.mk f)) : Γ(Q.L, W))
      = σ.val (op (Over.mk (homOfLE hUV))) :=
    σ.property (Over.homMk (homOfLE hUW) : Over.mk (homOfLE hUV) ⟶ Over.mk f).op
  have happ : Q.q.app U (E.presheaf.map (homOfLE hUW).op (show Γ(E, W) from s₀))
      = σ.val (op (Over.mk (homOfLE hUV))) :=
    h₁.trans ((congrArg (fun y : Γ(Q.L, W) => Q.L.presheaf.map (homOfLE hUW).op y)
      (hs.trans h₂)).trans h₃)
  rw [happ]
  exact ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over V)
    (op (Over.mk (homOfLE hUV)))).mapIso eV').toLinearEquiv.apply_symm_apply _

/-- **The cover on which the quotient splits, with the generator named.** This is
`exists_affine_open_splitting` with the frame forgotten: around every point there is an affine
open `U`, a section `s` of `E` over `U` and a section `t` of `Q.L` over `U` spanning `Γ(Q.L, U)`
with `q s = t`. -/
theorem exists_affine_open_splitting_span (Q : Stacks.Divisors.InvertibleQuotient X E) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ (t : Γ(Q.L, U)) (s : Γ(E, U)),
        Submodule.span Γ(X, U) {t} = ⊤ ∧ Q.q.app U s = t := by
  obtain ⟨U, hxU, hU, -, e, s, hs⟩ := exists_affine_open_splitting Q x
  exact ⟨U, hxU, hU, Q.q.app U s, s,
    eq_top_iff.2 fun y _ =>
      Submodule.mem_span_singleton.2 ⟨e y, e.injective (by simp [hs])⟩, rfl⟩

end Stacks.ProjectiveBundleConormal

end
