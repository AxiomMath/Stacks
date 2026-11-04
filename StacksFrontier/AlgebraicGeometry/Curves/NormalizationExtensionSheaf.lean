module

public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationExtensionSections
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationRawOpStalk
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationAffineCover
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationOwnStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components

/-!
# A vector field on an at-worst-nodal curve extends to the normalization

Let `k` be an algebraically closed field and `X` a reduced one-dimensional `k`-scheme, locally of
finite type, whose singularities are at worst nodal, and let `ν : X^ν ⟶ X` be its normalization.
This file produces, from a vector field `D` on `X`, the unique vector field `D'` on `X^ν` with
`D' (ν^♯ s) = ν^♯ (D s)` for every local section `s` of `𝒪_X`. That is the left-to-right
inclusion of Tag 0E68, read at the level of sheaves rather than of one affine open.

The affine-local data is already available: over the preimage of an affine open `U` of `X` the
vector field extends to an additive Leibniz map of `Γ(X^ν, ν⁻¹U)`, by
`Stacks.Curves.exists_leibniz_extension_normalizationSections`, and such a map is the value at
the top of a raw operator on the structure sheaf of `X^ν` over `ν⁻¹U`, by
`Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz`. What has to be supplied
here is the three things gluing asks for.

*The cover.* The affine opens of `X` cover `X`, so their preimages cover `X^ν`; each preimage is
affine because the normalization morphism is integral, hence affine
(`AlgebraicGeometry.IsAffineOpen.preimage`).

*The agreement on overlaps.* Two members of the cover meet in the preimage of the intersection of
two affine opens of `X`, which is again affine when the diagonal of `X` is affine — in particular
when `X` is separated. Over an affine open a raw operator is determined by its value at the top
(`Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext`), so the agreement reduces to the
agreement of the two values at the top over that intersection, which is
`Stacks.Curves.rawOp_eq_of_extension_of_extension`.

*The vanishing on the base.* The structural image of a global section of `𝒪_{Spec k}` in
`Γ(X^ν, ν⁻¹U)` is `ν^♯` of its structural image in `Γ(X, U)`, and a vector field annihilates the
latter; so the operator annihilates the former, its value at the top being `ν^♯` composed with
`D`.

Gluing is then `Stacks.Curves.existsUnique_sheafDerivationOf_of_affineCover`. The compatibility
`D' (ν^♯ s) = ν^♯ (D s)` comes out over the affine opens of `X` first, and is extended to every
open of `X` by covering it with affine opens and separating sections of `𝒪_{X^ν}` by their
restrictions. Uniqueness is proved the same way round: a second such vector field agrees with the
first over the preimage of each affine open, by
`Stacks.Curves.germ_eq_of_extension_of_extension`, and a vector field on a scheme is determined
by the map it induces on one stalk over each affine open
(`Stacks.Curves.eq_ownStalkFun_of_leibniz_of_germ`).

## Main results

* `Stacks.Curves.exists_rawOp_normalization_preimage` — over the preimage of an affine open of
  `X` a vector field on `X` is the value at the top of a natural Leibniz raw operator on the
  structure sheaf of the normalization.
* `Stacks.Curves.agreeOnCover_normalizationRawOps` — such a family of raw operators, one over
  each member of the cover of `X^ν` by the preimages of the affine opens of `X`, agrees on the
  opens contained in two members.
* `Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities` — **a vector
  field on an at-worst-nodal curve extends uniquely to a vector field on the normalization.**

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

section ExtensionSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Restricting a section along the inclusion of an open into itself does nothing. The morphism
`homOfLE h` for `h : W ≤ W` is not syntactically the identity, but the morphisms of a lattice of
opens between two fixed opens form a subsingleton. -/
private theorem presheaf_map_self {Z : Scheme.{u}} {W : Z.Opens} (h : W ≤ W) (x : Γ(Z, W)) :
    (Z.presheaf.map (homOfLE h).op).hom x = x := by
  have hid : (homOfLE h : W ⟶ W) = CategoryStruct.id W := Subsingleton.elim _ _
  rw [hid, op_id, Z.presheaf.map_id]
  rfl

/-- The comorphism of a morphism of schemes commutes with restriction of sections. -/
private theorem app_map_restrict {A : Scheme.{u}} (f : A ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    (A.presheaf.map (homOfLE hpre).op).hom ((f.app U).hom s)
      = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom s) := by
  have hcomp : f.app U ≫ A.presheaf.map (homOfLE hpre).op
      = X.presheaf.map (homOfLE h).op ≫ f.app V := by
    rw [Scheme.Hom.naturality]
    rfl
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(A, f ⁻¹ᵁ V) => φ.hom s) hcomp

/-- The restriction of a Leibniz raw operator to a slice of its base object is again Leibniz. -/
private theorem slice_unitOp_mul {T : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} T}
    {V V' : Opens T} {E : DiffOp.RawOp (SheafOfModules.unit O) (SheafOfModules.unit O) V}
    (hE : ∀ (W : Over V) (a b : O.obj.obj (op W.left)),
      E.unitOp W (a * b) = a * E.unitOp W b + b * E.unitOp W a)
    (h : V' ≤ V) (Z : Over V') (a b : O.obj.obj (op Z.left)) :
    (E.slice (Over.mk (homOfLE h))).unitOp Z (a * b)
      = a * (E.slice (Over.mk (homOfLE h))).unitOp Z b
        + b * (E.slice (Over.mk (homOfLE h))).unitOp Z a :=
  hE (Over.mk (Z.hom ≫ homOfLE h)) a b

/-- **The preimage of an affine open under the normalization is affine.** The normalization
morphism is integral (`AlgebraicGeometry.Scheme.isIntegralHom_normalization`), hence affine. -/
public theorem isAffineOpen_preimage_normalization
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (Scheme.normalization X hfin ⁻¹ᵁ U) := by
  have := Scheme.isIntegralHom_normalization (X := X) hfin
  exact hU.preimage (Scheme.normalization X hfin)

/-- **Every point of the preimage of an open `U` of `X` lies in the preimage of an affine open of
`X` contained in `U`**: the affine opens form a basis of the topology
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`). -/
public theorem exists_affineOpen_le_mem_preimage
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {q : Scheme.normalizationScheme X hfin}
    (hq : q ∈ Scheme.normalization X hfin ⁻¹ᵁ U) :
    ∃ V : X.affineOpens, (V : X.Opens) ≤ U ∧
      q ∈ Scheme.normalization X hfin ⁻¹ᵁ (V : X.Opens) := by
  obtain ⟨V, hV, hqV, hVU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hq
  exact ⟨⟨V, hV⟩, hVU, hqV⟩

/-- **The preimages of the affine opens of `X` cover the normalization.** This is
`Stacks.Curves.exists_affineOpen_le_mem_preimage` for the open `⊤`. -/
public theorem exists_mem_preimage_affineOpen
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (p : Scheme.normalizationScheme X hfin) :
    ∃ i : X.affineOpens, p ∈ Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens) := by
  obtain ⟨V, -, hpV⟩ := exists_affineOpen_le_mem_preimage hfin
    (show p ∈ Scheme.normalization X hfin ⁻¹ᵁ (⊤ : X.Opens) from Opens.mem_top p)
  exact ⟨V, hpV⟩

variable [IsAlgClosed k] [IsReduced X] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **Over the preimage of an affine open a vector field is the value at the top of a raw
operator.** Let `X` be a reduced one-dimensional `k`-scheme, locally of finite type over an
algebraically closed field, whose singularities are at worst nodal, and let `i` be an affine open
of `X`. Then there is a raw operator on the structure sheaf of the normalization over `ν⁻¹i`
which is compatible with restriction, obeys the Leibniz rule at every open contained in `ν⁻¹i`,
and whose value at the top carries `ν^♯` into `ν^♯` composed with the vector field.

The extension of the vector field to the sections over `ν⁻¹i` is
`Stacks.Curves.exists_leibniz_extension_normalizationSections`, and reading it as an operator
over the affine open `ν⁻¹i` is
`Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz`. -/
public theorem exists_rawOp_normalization_preimage
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (D : SheafDerivationOf (X ↘ Spec (.of k))) (i : X.affineOpens) :
    ∃ d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)),
      d.IsNatural ∧
      (∀ (W : Over (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))
        (a b : (Scheme.normalizationScheme X hfin).ringCatSheaf.obj.obj (op W.left)),
        d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a) ∧
      (∀ r : Γ(X, (i : X.Opens)),
        d.unitOp (Over.mk (CategoryStruct.id
            (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))))
            (((Scheme.normalization X hfin).app (i : X.Opens)).hom r)
          = ((Scheme.normalization X hfin).app (i : X.Opens)).hom (D.onSections r)) := by
  obtain ⟨E, hEmul, hEext⟩ :=
    exists_leibniz_extension_normalizationSections k X hfin hdim hnodal D i.2
  obtain ⟨d, hnat, hmul, hext⟩ :=
    Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz
      (isAffineOpen_preimage_normalization hfin i.2) E hEmul
  refine ⟨d, hnat, hmul, fun r => ?_⟩
  have h := hext (Over.mk (CategoryStruct.id
      (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))))
    (((Scheme.normalization X hfin).app (i : X.Opens)).hom r)
  rw [hEext r] at h
  simpa only [presheaf_map_self] using h

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The raw operators over the preimages of the affine opens agree on overlaps.** Two members
of the cover meet in the preimage of the intersection of two affine opens of `X`, affine because
the diagonal of `X` is affine; over an affine open a natural Leibniz raw operator is determined
by its value at the top
(`Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext`), and the two values at the top agree
there by `Stacks.Curves.rawOp_eq_of_extension_of_extension`. -/
public theorem agreeOnCover_normalizationRawOps
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (D : SheafDerivationOf (X ↘ Spec (.of k)))
    (d : ∀ i : X.affineOpens, DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))
    (hnat : ∀ i, (d i).IsNatural)
    (hmul : ∀ (i : X.affineOpens) (W : Over (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))
      (a b : (Scheme.normalizationScheme X hfin).ringCatSheaf.obj.obj (op W.left)),
      (d i).unitOp W (a * b) = a * (d i).unitOp W b + b * (d i).unitOp W a)
    (hdext : ∀ (i : X.affineOpens) (r : Γ(X, (i : X.Opens))),
      (d i).unitOp (Over.mk (CategoryStruct.id
          (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))))
          (((Scheme.normalization X hfin).app (i : X.Opens)).hom r)
        = ((Scheme.normalization X hfin).app (i : X.Opens)).hom (D.onSections r)) :
    DiffOp.AgreeOnCover
      (fun i : X.affineOpens => Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)) d := by
  refine DiffOp.agreeOnCover_of_slice_eq _ d fun i j => ?_
  have haff : IsAffineOpen (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens) ⊓
      Scheme.normalization X hfin ⁻¹ᵁ (j : X.Opens)) := by
    rw [← Scheme.Hom.preimage_inf]
    exact isAffineOpen_preimage_normalization hfin (IsAffineOpen.inf i.2 j.2)
  refine Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext haff _ _
    (AlgebraicGeometry.AffineDiffOp.raw_slice_natural (hnat i) _)
    (AlgebraicGeometry.AffineDiffOp.raw_slice_natural (hnat j) _)
    (slice_unitOp_mul (hmul i) inf_le_left) (slice_unitOp_mul (hmul j) inf_le_right) ?_
  exact rawOp_eq_of_extension_of_extension hfin D i.2 j.2 (d i) (hnat i) (hmul i) (hdext i)
    (d j) (hnat j) (hmul j) (hdext j) inf_le_left inf_le_right
    (normalization_preimage_le hfin inf_le_left) (normalization_preimage_le hfin inf_le_right)

omit [IsAlgClosed k] [IsReduced X] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The raw operator annihilates the structural image of a global section of the base.** The
structural map of `X^ν/Spec k` over `ν⁻¹i` factors as the structural map of `X/Spec k` over the
affine open `i` followed by `ν^♯`, so the value of the operator at the top turns it into `ν^♯` of
the value of the vector field on a section pulled back from the base, which vanishes. -/
public theorem unitOp_appLE_eq_zero
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (D : SheafDerivationOf (X ↘ Spec (.of k))) (i : X.affineOpens)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))
    (hdext : ∀ r : Γ(X, (i : X.Opens)),
      d.unitOp (Over.mk (CategoryStruct.id
          (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))))
          (((Scheme.normalization X hfin).app (i : X.Opens)).hom r)
        = ((Scheme.normalization X hfin).app (i : X.Opens)).hom (D.onSections r))
    (r : Γ(Spec (.of k), ⊤)) :
    d.unitOp (Over.mk (homOfLE (le_refl (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))))
        (((Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))).appLE ⊤
          (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)) le_top).hom r) = 0 := by
  have hle : (i : X.Opens) ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := le_top
  have harg := app_map_restrict (Scheme.normalization X hfin)
    (U := (X ↘ Spec (.of k)) ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)) (V := (i : X.Opens))
    hle le_top (((X ↘ Spec (.of k)).app ⊤).hom r)
  have hzero : D.onSections ((X.presheaf.map (homOfLE hle).op).hom
      (((X ↘ Spec (.of k)).app ⊤).hom r)) = 0 := by
    rw [D.onSections_restrict hle, D.onSections_app, map_zero]
  refine (congrArg (d.unitOp (Over.mk (homOfLE (le_refl
    (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)))))) harg).trans ?_
  refine (hdext _).trans ?_
  rw [hzero]
  exact map_zero ((Scheme.normalization X hfin).app (i : X.Opens)).hom

/-- **A vector field on an at-worst-nodal curve extends uniquely to the normalization.** Let `k`
be algebraically closed and `X` a reduced one-dimensional `k`-scheme, locally of finite type,
with affine diagonal — in particular a separated, for instance proper, one — whose singularities
are at worst nodal, and suppose the quasi-compact opens of `X` have finitely many irreducible
components, so that the normalization `ν : X^ν ⟶ X` exists. Then every vector field `D` on `X`
has a unique extension to a vector field `D'` on `X^ν`, in the sense that
`D' (ν^♯ s) = ν^♯ (D s)` for every local section `s` of `𝒪_X`.

This is the left-to-right inclusion of Tag 0E68 at the level of sheaves: the extensions built
over the preimages of the affine opens of `X` by
`Stacks.Curves.exists_rawOp_normalization_preimage` agree on overlaps by
`Stacks.Curves.agreeOnCover_normalizationRawOps` and glue by
`Stacks.Curves.existsUnique_sheafDerivationOf_of_affineCover`.

That the extension fixes the points over the nodes, so that it lies in the right-hand side of
the tag's equality, is
`Stacks.Curves.existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities`. -/
public theorem existsUnique_extend_normalization_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from X))]
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (D : SheafDerivationOf (X ↘ Spec (.of k))) :
    ∃! D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))),
      ∀ (U : X.Opens) (s : Γ(X, U)),
        D'.onSections (((Scheme.normalization X hfin).app U).hom s)
          = ((Scheme.normalization X hfin).app U).hom (D.onSections s) := by
  choose d hnat hmul hdext using
    exists_rawOp_normalization_preimage (k := k) (X := X) hfin hdim hnodal D
  obtain ⟨D', hD', -⟩ := existsUnique_sheafDerivationOf_of_affineCover
    (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k)))
    (fun i : X.affineOpens => Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))
    (exists_mem_preimage_affineOpen hfin) d hnat
    (agreeOnCover_normalizationRawOps hfin D d hnat hmul hdext) hmul
    fun i r => unitOp_appLE_eq_zero hfin D i (d i) (hdext i) r
  have haffine : ∀ (i : X.affineOpens) (s : Γ(X, (i : X.Opens))),
      D'.onSections (((Scheme.normalization X hfin).app (i : X.Opens)).hom s)
        = ((Scheme.normalization X hfin).app (i : X.Opens)).hom (D.onSections s) := by
    intro i s
    rw [hD' i (Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens)) le_rfl]
    exact hdext i s
  have key : ∀ (D₁ : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k)))),
      (∀ (i : X.affineOpens) (s : Γ(X, (i : X.Opens))),
        D₁.onSections (((Scheme.normalization X hfin).app (i : X.Opens)).hom s)
          = ((Scheme.normalization X hfin).app (i : X.Opens)).hom (D.onSections s)) →
      ∀ (U : X.Opens) (s : Γ(X, U)),
        D₁.onSections (((Scheme.normalization X hfin).app U).hom s)
          = ((Scheme.normalization X hfin).app U).hom (D.onSections s) := by
    intro D₁ h₁ U s
    refine TopCat.Presheaf.IsSheaf.section_ext
      (Scheme.normalizationScheme X hfin).sheaf.cond fun q hq => ?_
    obtain ⟨V, hVU, hqV⟩ := exists_affineOpen_le_mem_preimage hfin hq
    have hle := normalization_preimage_le hfin hVU
    refine ⟨Scheme.normalization X hfin ⁻¹ᵁ (V : X.Opens), hle, hqV, ?_⟩
    show ((Scheme.normalizationScheme X hfin).presheaf.map (homOfLE hle).op).hom
          (D₁.onSections (((Scheme.normalization X hfin).app U).hom s))
        = ((Scheme.normalizationScheme X hfin).presheaf.map (homOfLE hle).op).hom
          (((Scheme.normalization X hfin).app U).hom (D.onSections s))
    rw [← D₁.onSections_restrict hle, app_map_restrict _ hVU hle, app_map_restrict _ hVU hle,
      ← D.onSections_restrict hVU]
    exact h₁ V _
  refine ⟨D', key D' haffine, fun D₂ h₂ => ?_⟩
  have hsec : ∀ (i : X.affineOpens)
      (z : Γ(Scheme.normalizationScheme X hfin,
        Scheme.normalization X hfin ⁻¹ᵁ (i : X.Opens))),
      D₂.onSections z = D'.onSections z := by
    intro i z
    refine section_eq_of_germ_eq hfin _ _ fun p hp => ?_
    exact germ_eq_of_extension_of_extension hfin D i.2 i.2
      (AddMonoidHom.mk' (fun w => D₂.onSections w) fun a b => D₂.onSections_add a b)
      (fun a b => D₂.onSections_mul a b) (fun r => h₂ (i : X.Opens) r)
      (AddMonoidHom.mk' (fun w => D'.onSections w) fun a b => D'.onSections_add a b)
      (fun a b => D'.onSections_mul a b) (fun r => haffine i r) hp hp z z rfl
  refine SheafDerivationOf.ext' fun V z => ?_
  refine TopCat.Presheaf.IsSheaf.section_ext
    (Scheme.normalizationScheme X hfin).sheaf.cond (U := op V) fun q hq => ?_
  obtain ⟨i, hqi⟩ := exists_mem_preimage_affineOpen hfin q
  have hstalk := eq_ownStalkFun_of_leibniz_of_germ D'
    (isAffineOpen_preimage_normalization hfin i.2) hqi (ownStalkAddHom D₂ q)
    (fun a b => ownStalkFun_mul D₂ a b) fun w => by
      rw [ownStalkAddHom_apply, ownStalkFun_germ, hsec i w]
  have hgerm : (Scheme.normalizationScheme X hfin).presheaf.germ V q hq (D₂.onSections z)
      = (Scheme.normalizationScheme X hfin).presheaf.germ V q hq (D'.onSections z) := by
    rw [← ownStalkFun_germ D₂ V hq z, ← ownStalkFun_germ D' V hq z]
    exact hstalk _
  obtain ⟨W, hqW, iV, iV', heq⟩ :=
    (Scheme.normalizationScheme X hfin).presheaf.germ_eq q hq hq
      (D₂.onSections z) (D'.onSections z) hgerm
  exact ⟨W, iV.le, hqW, heq⟩

end ExtensionSheaf

end Stacks.Curves

end
