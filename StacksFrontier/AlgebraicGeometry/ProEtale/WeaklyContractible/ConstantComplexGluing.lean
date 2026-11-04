module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafProjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantClopenPieces
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.CategoryTheory.Sites.Glueing.DerivedIsoGlue

/-!
# Complexes locally isomorphic to a constant complex, over a w-contractible affine

Let `X` be a scheme, `R` a ring, `L` an object of `D(X_proét, R)` and `N` a bounded above complex
of projective `R`-modules. Suppose that every object of `X_proét` has a covering on whose members
`L` is isomorphic to the constant complex `\underline{N}`, with no compatibility between these
isomorphisms. Then over every affine object `V` of `X_proét` whose ring of global sections is
w-contractible, the restriction of `L` is isomorphic to `\underline{N}`.

The covering of `V` is refined by a finite decomposition `V = ∐ V_i` into disjoint clopen pieces
(Stacks 098H), each again affine with w-contractible global sections. Over such an object global
sections are exact, so `\underline{N}` is a bounded above complex of projectives and each given
isomorphism over `V_i` comes from a quasi-isomorphism of complexes. Maps of sheaves glue along
the decomposition with no compatibility condition, so these quasi-isomorphisms glue to a morphism
of complexes over `V`, which is a quasi-isomorphism because invertibility is local.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.isAffineWContractible_clopenDecompositionObj`: the pieces of a
  clopen decomposition of an affine object with w-contractible global sections are again such.
* `AlgebraicGeometry.Scheme.ProEt.projective_constantSheaf_over_of_isAffineWContractible`: the
  constant sheaf on a projective module is projective on the slice site over such an object.
* `AlgebraicGeometry.Scheme.ProEt.bijective_overMapPullback_map_clopenDecomposition`: maps of
  sheaves glue along a clopen decomposition.
* `AlgebraicGeometry.ProEtale.nonempty_overPullback_iso_constantSheaf_of_isAffineWContractible`:
  the main result.

## References

* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible Stacks.SheafMapGluing

universe w u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- **The pieces of a clopen decomposition of a w-contractible affine are w-contractible
affines.** Each piece is isomorphic to a clopen open subscheme
(`AlgebraicGeometry.ProEtale.isAffine_and_isWContractible_of_isClopen`). -/
theorem isAffineWContractible_clopenDecompositionObj {W : S.ProEt}
    (hW : IsAffineWContractible W) {n : ℕ} {U : Fin n → Scheme.{u}}
    {f : (i : Fin n) → U i ⟶ W.left} (hdec : IsClopenDecompositionCover U f)
    (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) (i : Fin n) :
    IsAffineWContractible (clopenDecompositionObj W f hf i) := by
  obtain ⟨hA, hC⟩ := hW
  have := hdec.openImmersion i
  obtain ⟨h₁, h₂⟩ := ProEtale.isAffine_and_isWContractible_of_isClopen hC (f i).opensRange
    (by simpa using hdec.clopen i)
  let e := (f i).isoOpensRange
  have : IsAffine (U i) := .of_isIso e.hom
  exact ⟨this, ProEtale.isWContractible_of_ringEquiv
    (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm h₂⟩

variable {R : Type (max (u + 1) w)} [Ring R]

/-- **The constant sheaf on a projective module is projective over a w-contractible affine.** On
the slice site over an affine object of `S_proét` with w-contractible global sections, sections
over the final object are exact
(`AlgebraicGeometry.Scheme.ProEt.surjective_app_over_of_isWContractible`),
so the constant sheaf on a projective module is projective. -/
theorem projective_constantSheaf_over_of_isAffineWContractible {W : S.ProEt}
    (hW : IsAffineWContractible W) (M : ModuleCat.{max (u + 1) w} R) [Projective M] :
    Projective ((constantSheaf ((ProEt.topology S).over W) (ModuleCat.{max (u + 1) w} R)).obj M) :=
  have := hW.1
  Stacks.ConstantSheaf.projective_constantSheaf_of_surjective_app _ R Over.mkIdTerminal
    (fun φ hφ => surjective_app_over_of_isWContractible W hW.2 φ hφ) M

/-- **Maps of sheaves glue along a clopen decomposition**, with no compatibility condition. For a
finite decomposition of an object `W` of `S_proét` into disjoint clopen pieces `W_i`, restriction
along the `W_i ⟶ W` is a bijection from maps between the restrictions of two sheaves to `S_proét/W`
onto families of maps between their restrictions to the `S_proét/W_i`: this is
`AlgebraicGeometry.Scheme.ProEt.bijective_restrict_clopenDecomposition` for the sheaf of
morphisms. -/
theorem bijective_overMapPullback_map_clopenDecomposition {A : Type*} [Category A]
    (F G : Sheaf (ProEt.topology S) A) (W : S.ProEt) {n : ℕ} {U : Fin n → Scheme.{u}}
    {f : (i : Fin n) → U i ⟶ W.left} (hdec : IsClopenDecompositionCover U f)
    (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) :
    Function.Bijective (fun (ψ : ((ProEt.topology S).overPullback A W).obj F ⟶
        ((ProEt.topology S).overPullback A W).obj G) (i : Fin n) =>
      ((ProEt.topology S).overMapPullback A (clopenDecompositionHom W f hf i)).map ψ) :=
  bijective_restrict_clopenDecomposition (sheafHom F G) W f hdec hf

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **A complex locally isomorphic to a constant complex is so over a w-contractible affine.**
Let `L` be an object of `D(X_proét, R)` and `N` a bounded above complex of projective
`R`-modules such that every object of `X_proét` has a covering on whose members `L` is isomorphic
to the constant complex `\underline{N}`. Then the restriction of `L` to every affine object `V`
of `X_proét` with w-contractible ring of global sections is isomorphic to `\underline{N}`.

The covering of `V` is refined by a finite clopen decomposition `V = ∐ V_i`
(`AlgebraicGeometry.Scheme.ProEt.exists_clopenDecomposition_of_isWContractible`); the given
isomorphisms restrict to the `V_i`, over which `\underline{N}` is a bounded above complex of
projectives
(`AlgebraicGeometry.Scheme.ProEt.projective_constantSheaf_over_of_isAffineWContractible`);
maps of sheaves glue along the decomposition
(`AlgebraicGeometry.Scheme.ProEt.bijective_overMapPullback_map_clopenDecomposition`) and
invertibility is local (`CategoryTheory.Sheaf.isIso_of_isIso_overMapPullback_map`), so
`DerivedCategory.nonempty_Q_obj_iso_of_forall_iso_map` applies. -/
theorem nonempty_overPullback_iso_constantSheaf_of_isAffineWContractible
    {R : Type (max (u + 1) w)} [CommRing R]
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)))
    (N : CochainComplex (ModuleCat.{max (u + 1) w} R) ℤ) (b : ℤ)
    [N.IsStrictlyLE b] (hN : ∀ k, Module.Projective R (N.X k))
    (hloc : ∀ U : X.ProEt, ∃ (ι : Type (u + 1)) (W : ι → X.ProEt) (g : ∀ j, W j ⟶ U),
      Sieve.ofArrows W g ∈ Scheme.ProEt.topology X U ∧ ∀ j, Nonempty
        (((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} R)
          (W j)).mapDerivedCategory.obj L ≅
        DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over (W j))
          (ModuleCat.{max (u + 1) w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))
    (V : X.ProEt) (hV : Scheme.ProEt.IsAffineWContractible V) :
    Nonempty (((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} R)
          V).mapDerivedCategory.obj L ≅
        DerivedCategory.Q.obj (((constantSheaf ((Scheme.ProEt.topology X).over V)
          (ModuleCat.{max (u + 1) w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) := by
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) w} R
  let up := ComplexShape.up ℤ
  -- a complex representing `L`, and the complex of constant sheaves on `X_proét`
  let K := DerivedCategory.Q.objPreimage L
  let eK : DerivedCategory.Q.obj K ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let F := (constantSheaf J A).mapHomologicalComplex up |>.obj N
  -- the constant complex on a slice is the restriction of `F`
  let cIso (U : X.ProEt) : ((constantSheaf (J.over U) A).mapHomologicalComplex up).obj N ≅
      ((J.overPullback A U).mapHomologicalComplex up).obj F :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k => (Stacks.ConstantSheaf.overPullbackConstantSheafIso J A U).app (N.X k))
      (fun _ _ _ =>
        ((Stacks.ConstantSheaf.overPullbackConstantSheafIso J A U).hom.naturality _).symm)
  -- the restriction of `L` is represented by the restriction of `K`
  let lIso (U : X.ProEt) : (J.overPullback A U).mapDerivedCategory.obj L ≅
      DerivedCategory.Q.obj (((J.overPullback A U).mapHomologicalComplex up).obj K) :=
    (J.overPullback A U).mapDerivedCategory.mapIso eK.symm ≪≫
      (J.overPullback A U).mapDerivedCategoryFactors.app K
  suffices h : Nonempty
      (DerivedCategory.Q.obj (((J.overPullback A V).mapHomologicalComplex up).obj F) ≅
      DerivedCategory.Q.obj (((J.overPullback A V).mapHomologicalComplex up).obj K)) by
    obtain ⟨e⟩ := h
    exact ⟨lIso V ≪≫ e.symm ≪≫ DerivedCategory.Q.mapIso (cIso V).symm⟩
  -- refine the covering of `V` by a clopen decomposition
  obtain ⟨ι, W, g, hcov, hiso⟩ := hloc V
  have hA : IsAffine V.left := hV.1
  obtain ⟨n, U, f, hdec, hf, hR⟩ :=
    Scheme.ProEt.exists_clopenDecomposition_of_isWContractible V hV.2 _ hcov
  let Vi := Scheme.ProEt.clopenDecompositionObj V f hf
  let fi := Scheme.ProEt.clopenDecompositionHom V f hf
  -- the given isomorphisms, restricted to the pieces
  have hpiece (i : Fin n) : Nonempty
      (DerivedCategory.Q.obj (((J.overPullback A (Vi i)).mapHomologicalComplex up).obj F) ≅
        DerivedCategory.Q.obj (((J.overPullback A (Vi i)).mapHomologicalComplex up).obj K)) := by
    obtain ⟨j, a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 (hR i)
    obtain ⟨e⟩ := hiso j
    exact nonempty_Q_obj_overPullback_iso_of_hom J a F K
      (DerivedCategory.Q.mapIso (cIso (W j)).symm ≪≫ e.symm ≪≫ lIso (W j))
  have e := fun i => (hpiece i).some
  let E (i : Fin n) := J.overMapPullback A (fi i)
  have hcovV : Sieve.ofArrows Vi fi ∈ J V :=
    Scheme.ProEt.sieve_ofArrows_clopenDecomposition_mem_topology V f hdec hf
  have hzero (k : ℤ) (hk : b < k) (i : Fin n) :
      IsZero ((E i).obj ((J.overPullback A V).obj ((constantSheaf J A).obj (N.X k)))) :=
    (E i).map_isZero ((J.overPullback A V).map_isZero
      ((constantSheaf J A).map_isZero (N.isZero_of_isStrictlyLE b k hk)))
  have : ∀ i, CochainComplex.IsStrictlyLE
      (((E i).mapHomologicalComplex up).obj (((J.overPullback A V).mapHomologicalComplex up).obj F))
      b := fun i => (CochainComplex.isStrictlyLE_iff _ _).2 fun k hk => hzero k hk i
  have : ∀ i k, Projective ((((E i).mapHomologicalComplex up).obj
      (((J.overPullback A V).mapHomologicalComplex up).obj F)).X k) := fun i k => by
    have : Projective (N.X k) := (IsProjective.iff_projective (N.X k)).1 (hN k)
    have := Scheme.ProEt.projective_constantSheaf_over_of_isAffineWContractible
      (Scheme.ProEt.isAffineWContractible_clopenDecompositionObj hV hdec hf i) (N.X k)
    exact Projective.of_iso ((overPullbackOverMapPullbackIso J (fi i) (A := A)).app _ ≪≫
      (Stacks.ConstantSheaf.overPullbackConstantSheafIso J A (Vi i)).symm.app (N.X k)).symm this
  refine DerivedCategory.nonempty_Q_obj_iso_of_forall_iso_map E
    (fun ψ hψ => Sheaf.isIso_of_isIso_overMapPullback_map J fi hcovV ψ hψ) _ _ ?_ ?_
    (fun _ => b) (fun i => DerivedCategory.Q.mapIso (overMapPullbackComplexIso J (fi i) F) ≪≫
      e i ≪≫ DerivedCategory.Q.mapIso (overMapPullbackComplexIso J (fi i) K).symm)
  · intro k l φ ψ h
    exact (Scheme.ProEt.bijective_overMapPullback_map_clopenDecomposition (F.X k) (K.X l) V hdec
      hf).1 (funext h)
  · intro k φ
    exact (Scheme.ProEt.bijective_overMapPullback_map_clopenDecomposition (F.X k) (K.X k) V hdec
      hf).2 φ |>.imp fun ψ hψ i => congrFun hψ i

end AlgebraicGeometry.ProEtale
